-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_assumptions .fsplit .automatic_induction .tidy_attributes .intro_at_least_one
import .monadic_chain
import .smt
import .reducible_abstract
-- import .simp_at_each
import .rewrite_search
import .injections

import tactic.interactive

import data.list

open tactic

universe variable u

attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b has_coe_to_fun.coe
attribute [reducible] eq.mpr
attribute [ematch] subtype.property

meta def dsimp' := `[dsimp {unfold_reducible := tt, md := semireducible}]
meta def dsimp_all' := `[dsimp at * {unfold_reducible := tt, md := semireducible}]

-- TODO I'd love to do some profiling here, and find how much time is spent inside each tactic,
-- also divided up between successful and unsuccessful calls.

-- TODO also find tactics which are never used!

meta def my_solve_by_elim (asms : option (list expr) := none)  : opt_param ℕ 3 → tactic unit
| 0 := tactic.done
| (n+1) :=
tactic.interactive.apply_assumption asms $ cc <|> my_solve_by_elim n

-- TODO does cc help?
meta def tidy_tactics : list (tactic string) :=
[
  -- terminal_goal >> assumption >> pure "assumption",
  -- terminal_goal >> congr_assumptions,
  force (reflexivity)                         >> pure "refl", 
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  semiapplicable                              >>= λ n, pure ("fapply " ++ n.to_string),
  applicable                                  >>= λ n, pure ("fapply " ++ n.to_string),
  intro_at_least_one                          >> pure "intros",
  automatic_induction                         >> pure "automatic_induction",
  force (fsplit)                              >> pure "fsplit", 
  `[dsimp]                                    >> pure "dsimp",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[unfold_projs]                             >> pure "unfold_projs",
  `[unfold_projs at *]                        >> pure "unfold_projs at *",
  `[simp!]                                    >> pure "simp!",
  `[simp! at *]                               >> pure "simp! at *",
  injections_and_clear                        >> pure "injections_and_clear",
  terminal_goal >> (cc <|> my_solve_by_elim)  >> pure "solve_by_elim",
  dsimp'                                      >> pure "dsimp'",
  dsimp_all'                                  >> pure "dsimp_all'",
  run_tidy_tactics
]

private meta def any_later_goals_core { α : Type } (tac : tactic α) : list expr → list expr → list (option α) → bool → tactic (list (option α))
| []        ac results progress := guard progress >> set_goals ac >> pure results
| (g :: gs) ac results progress :=
  do set_goals [g],
     succeeded ← try_core tac,
     new_gs    ← get_goals,
     any_later_goals_core gs (ac ++ new_gs) (succeeded :: results) (succeeded.is_some || progress)

/-- Apply the given tactic to any goal besides the first where it succeeds. The tactic succeeds only if
   tac succeeds for at least one goal. -/
meta def any_later_goals { α : Type } (tac : tactic α ) : tactic (list (option α)) :=
do gs ← get_goals,
   any_later_goals_core tac gs [] [] ff

meta def tactics_on_later_goals (tactics : list (tactic string)) :=
tactics.map(λ t, any_later_goals t >>= λ s, pure ("tactic.focus [ " ++ ((((none :: s).map(λ o, option.get_or_else (option.map (λ m, "`[" ++ m ++ "]") o) "tactic.skip")).intersperse ", ").foldl append "") ++ "]"))

meta structure tidy_cfg extends chain_cfg :=
( trace_result : bool    := ff )
( show_hints   : bool    := ff )
( hints        : list ℕ  := [] )
( later_goals  : bool    := tt )
( extra_tactics : list (tactic string) := [] )

private meta def number_tactics { α : Type } ( tactics : list (tactic α) ) : list ( tactic (α × ℕ) ) :=
tactics.map₂ ( λ t, λ n, (do r ← t, pure (r, n))) (list.range tactics.length)

private meta def apply_hints { α : Type } ( tactics : list (tactic α) ) : list ℕ → tactic bool
| list.nil  := pure tt
| (n :: ns) := match tactics.nth n with
               | none := pure ff
               | some t := if_then_else t (apply_hints ns) (pure ff)
               end

meta def tidy ( cfg : tidy_cfg := {} ) : tactic unit :=
let tactics := tidy_tactics ++ cfg.extra_tactics in
let tactics := tactics
                     ++ (if cfg.later_goals then tactics_on_later_goals tactics else []) in
let numbered_tactics := number_tactics tactics in
do
   /- first apply hints -/
   continue ← (if ¬ cfg.hints.empty then
                  do 
                     r ← apply_hints numbered_tactics cfg.hints,
                     if ¬ r then
                      /- hints were broken ... -/     
                        do
                          interaction_monad.trace "hints for 'tidy' tactic were invalid!",
                          interaction_monad.fail "hints for 'tidy' tactic were invalid!" -- this will be trapped a moment later
                     else
                        pure ff
                else
                  pure tt) <|> pure tt,
   if continue then               
    do
      results ← chain numbered_tactics cfg.to_chain_cfg,
      try tactic.interactive.resetI, -- FIXME reset the typeclass inference cache, since `dsimp at *` may have spoiled it: https://github.com/leanprover/lean/issues/1920
      if cfg.show_hints ∨ ¬ cfg.hints.empty then
        let hints := results.map (λ p, p.2) in
        interaction_monad.trace ("tidy {hints:=" ++ hints.to_string ++ "}")
      else 
        tactic.skip,
      if cfg.trace_result then
        let result_strings := results.map (λ p, p.1) in
        interaction_monad.trace ("chain tactic used: " ++ result_strings.to_string)
      else
        tactic.skip
   else
     tactic.skip


meta def obviously_tactics : list (tactic string) :=
[
  -- force ( smt_eblast) >> pure "smt_eblast",
  `[rewrite_search_using `ematch] >> pure "rewrite_search_using `ematch"
]

meta def obviously := reducible_abstract (
  tidy { extra_tactics := obviously_tactics }
)

-- TODO obviously!, which uses solve_by_elim even on unsafe goals

notation `♮` := by reducible_abstract { smt_eblast }
notation `♯`  := by obviously

example : 1 = 1 := ♯ 