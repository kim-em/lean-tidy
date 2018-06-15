-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .fsplit .automatic_induction .tidy_attributes .intro_at_least_one
import .chain
import .recover
import .reducible_abstract
import .rewrite_search
import .injections
import .simplify_proof
import .if_then_else
import tactic.interactive

import data.list

universe variables u v

attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b has_coe_to_fun.coe
attribute [reducible] eq.mpr
attribute [ematch] subtype.property

meta def dsimp' := `[dsimp {unfold_reducible := tt, md := semireducible}]
meta def dsimp_all' := `[dsimp at * {unfold_reducible := tt, md := semireducible}]

lemma funext_simp {α : Type u} {Z : α → Type v} {f g : Π a : α, Z a} : (f = g) = ∀ a : α, f a = g a :=
begin
  apply propext,
  split,
  { intro w, intro, rw w },
  { intro w, apply funext, assumption }
end 

open tactic

-- TODO I'd love to do some profiling here, and find how much time is spent inside each tactic,
-- also divided up between successful and unsuccessful calls.

-- TODO also find tactics which are never used!

meta def default_tidy_tactics : list (tactic string) :=
[
  force (reflexivity)                         >> pure "refl", 
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  semiapplicable                              >>= λ n, pure ("apply " ++ n.to_string ++ " ; assumption"),
  applicable                                  >>= λ n, pure ("apply " ++ n.to_string),
  intro_at_least_one                          >> pure "intros",
  automatic_induction,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[unfold_coes]                              >> pure "unfold_coes",
  `[dsimp]                                    >> pure "dsimp",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp]                                     >> pure "simp",
  `[simp at *]                                >> pure "simp at *",
  force (fsplit)                              >> pure "fsplit", 
  injections_and_clear                        >> pure "injections_and_clear",
  terminal_goal >> (`[solve_by_elim {discharger := `[cc]}])  >> pure "solve_by_elim {discharger := `[cc]}",
  `[simp only [funext_simp] at *]             >> pure "simp only [funext_simp] at *",
  `[dsimp {unfold_reducible:=tt}]             >> pure "dsimp {unfold_reducible:=tt}",
  run_tidy_tactics
]

private meta def any_later_goals_core { α : Type } (tac : tactic α) (first_goal : expr) : list expr → list expr → list (option α) → bool → tactic (list (option α))
| []        ac results progress := guard progress >> set_goals (first_goal :: ac) >> pure results.reverse
| (g :: gs) ac results progress :=
  do set_goals [g],
     succeeded ← try_core tac,
     new_gs    ← get_goals,
     any_later_goals_core gs (ac ++ new_gs) (succeeded :: results) (succeeded.is_some || progress)

/-- Apply the given tactic to any goal besides the first where it succeeds. The tactic succeeds only if
   tac succeeds for at least one goal. -/
meta def any_later_goals { α : Type } (tac : tactic α ) : tactic (list (option α)) :=
do gs ← get_goals,
   any_later_goals_core tac gs.head gs.tail [] [] ff

meta def tactics_on_later_goals (tactics : list (tactic string)) :=
tactics.map(λ t, any_later_goals t >>= λ s, pure ("tactic.focus [" ++ ((((none :: s).map(λ o, option.get_or_else (option.map (λ m, "`[" ++ m ++ "]") o) "tactic.skip")).intersperse ", ").foldl append "") ++ "]"))

meta structure tidy_cfg extends chain_cfg :=
( trace_result : bool    := ff )
( show_hints   : bool    := ff )
( hints        : list ℕ  := [] )
( later_goals  : bool    := tt )
( tactics : list (tactic string) := default_tidy_tactics )

private meta def number_tactics { α : Type } ( tactics : list (tactic α) ) : list ( tactic (α × ℕ) ) :=
tactics.map₂ ( λ t, λ n, (do r ← t, pure (r, n))) (list.range tactics.length)

private meta def apply_hints { α : Type } ( tactics : list (tactic α) ) : list ℕ → tactic bool
| list.nil  := pure tt
| (n :: ns) := match tactics.nth n with
               | none := pure ff
               | some t := if_then_else t (apply_hints ns) (pure ff)
               end

meta def tidy ( cfg : tidy_cfg := {} ) : tactic unit :=
let tactics := cfg.tactics in
let tactics := tactics ++ (if cfg.later_goals then tactics_on_later_goals tactics else []) in
let numbered_tactics := number_tactics tactics in
do
   /- first apply hints -/
   continue ← (if ¬ cfg.hints.empty then
                  do 
                     r ← apply_hints numbered_tactics cfg.hints,
                     if ¬ r then
                      /- hints were broken ... -/     
                        do
                          trace "hints for 'tidy' tactic were invalid!",
                          failed -- this will be trapped a moment later
                     else
                        pure ff
                else
                  pure tt) <|> pure tt,
   if continue then               
    do
      results ← chain cfg.to_chain_cfg numbered_tactics,
      try tactic.interactive.resetI,
      if cfg.show_hints ∨ ¬ cfg.hints.empty then
        let hints := results.map (λ p, p.2) in
        trace ("tidy {hints:=" ++ hints.to_string ++ "}")
      else 
        tactic.skip,
      if cfg.trace_result then
        let result_strings := results.map (λ p, p.1) in
        trace ("---\n" ++ (",\n".intercalate result_strings) ++ "\n---")
      else
        tactic.skip
   else
     tactic.skip

meta def obviously_tactics : list (tactic string) :=
[
  tactic.interactive.rewrite_search_using `ematch -- TODO should switch this back to search eventually
]

meta def obviously : tactic unit := all_goals ( abstract ( -- TODO this is a bit gross
  tidy { tactics := default_tidy_tactics ++ obviously_tactics }
))

meta def obviously' : tactic unit := all_goals ( abstract (
  tidy { tactics := default_tidy_tactics ++ obviously_tactics, trace_result := tt }
))

example : 1 = 1 := by obviously

instance subsingleton_pempty : subsingleton pempty := by tidy
instance subsingleton_punit  : subsingleton punit  := by tidy
