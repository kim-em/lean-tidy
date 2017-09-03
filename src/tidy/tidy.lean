-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_assumptions .fsplit .automatic_induction .tidy_attributes .intro_at_least_one
import .monadic_chain
import .smt

import data.list

open tactic

universe variable u

attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b has_coe_to_fun.coe
attribute [ematch] subtype.property

private meta def dsimp_eq_mpr : tactic unit := `[dsimp [eq.mpr] {unfold_reducible := tt}]
meta def dsimp' := `[dsimp {unfold_reducible := tt, md := semireducible}]
meta def dsimp_all' := `[dsimp at * {unfold_reducible := tt, md := semireducible}]

meta def if_exactly_one_goal { α : Type } ( t : tactic α ) : tactic α :=
do ng ← num_goals,
   if ng = 1 then t else fail "there is not exactly one goal"

meta def build_focus_string ( s : list ( option string ) ) : tactic string := 
pure ("focus " ++ (s.map(λ x, option.get_or_else x "skip")).to_string)

meta def if_first_goal_safe { α : Type } ( t : tactic α ) : tactic α :=
do ng ← num_goals,
   if ng = 1 then t else do {
     p ← target >>= is_prop,
     if p then t else fail "there are multiple goals, and the first goal is not a mere proposition"
   }

-- TODO I'd love to do some profiling here, and find how much time is spent inside each tactic,
-- also divided up between successful and unsuccessful calls.

-- TODO also find tactics which are never used!

-- TODO does cc help?
meta def unsafe_tidy_tactics : list (tactic string) :=
[
  assumption >> pure "assumption",
  congr_assumptions,
  `[simp only [id_locked_eq]]                 >> pure "simp only [id_locked_eq]"
]

meta def safe_tidy_tactics : list (tactic string) :=
[
  force (reflexivity)                         >> pure "refl", 
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  applicable                                  >>= λ n, pure ("fapply " ++ n.to_string),
  intro_at_least_one                          >> pure "intros",
  force (fsplit)                              >> pure "fsplit", 
  dsimp'                                      >> pure "dsimp'",
  `[simp]                                     >> pure "simp",
  automatic_induction                         >> pure "automatic_induction",
  dsimp_all'                                  >> pure "dsimp_all'",
  `[simp at *]                                >> pure "simp at *"
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

meta def global_tidy_tactics :=
unsafe_tidy_tactics.map(if_first_goal_safe)
++ safe_tidy_tactics

meta def safe_tactics_on_later_goals :=
safe_tidy_tactics.map(λ t, any_later_goals t >>= λ s, pure ("tactic.focus [ " ++ ((((none :: s).map(λ o, option.get_or_else o "skip")).intersperse ", ").foldl append "") ++ "]"))

meta structure tidy_cfg extends chain_cfg :=
( trace_result          : bool                 := ff )
( run_annotated_tactics : bool                 := tt )
( extra_tactics         : list (tactic string) := [] )
( show_hints            : bool                 := ff )
( hints                 : list ℕ               := [] )
( later_goals           : bool                 := tt )

private meta def number_tactics { α : Type } ( tactics : list (tactic α) ) : list ( tactic (α × ℕ) ) :=
tactics.map₂ ( λ t, λ n, (do r ← t, pure (r, n))) (list.range tactics.length)

private meta def apply_hints { α : Type } ( tactics : list (tactic α) ) : list ℕ → tactic bool
| list.nil  := pure tt
| (n :: ns) := match tactics.nth n with
               | none := pure ff
               | some t := if_then_else t (apply_hints ns) (pure ff)
               end
meta def tidy ( cfg : tidy_cfg := {} ) : tactic unit :=
let tidy_tactics := global_tidy_tactics
                     ++ (if cfg.later_goals then safe_tactics_on_later_goals else []) 
                     ++ (if cfg.run_annotated_tactics then [ run_tidy_tactics ] else []) 
                     ++ cfg.extra_tactics in
let numbered_tactics := number_tactics tidy_tactics in
do
   /- first apply hints -/
   if ¬ cfg.hints.empty then
     do r ← apply_hints numbered_tactics cfg.hints,
      if ¬ r then
        /- hints were broken ... -/     
          trace "hints for 'tidy' tactic were invalid!"     
      else
          skip
   else
    do
      original_goals ← get_goals,
      results ← chain numbered_tactics cfg.to_chain_cfg,
      if cfg.show_hints then
        let hints := results.map (λ p, p.2) in
        trace ("tidy {hints:=" ++ hints.to_string ++ "}")
      else 
        skip,
      if cfg.trace_result then
        let result_strings := results.map (λ p, p.1) in
        trace ("chain tactic used: " ++ result_strings.to_string)
      else
        skip

meta def blast ( cfg : tidy_cfg := {} ) : tactic unit := 
tidy { cfg with extra_tactics := cfg.extra_tactics ++ [ focus1 ( smt_eblast >> tactic.done ) >> pure "smt_eblast" ] }

notation `♮` := by abstract { smt_eblast }
notation `♯`  := by abstract { blast }

-- meta def interactive_simp := `[simp]

def tidy_test_0 : ∀ x : unit, x = unit.star := 
begin
  success_if_fail { chain [ interactive_simp ] },
  intro1,
  induction x,
  refl
end


def tidy_test (a : string): ∀ x : unit, x = unit.star := 
begin
  tidy {show_hints := tt}
end
