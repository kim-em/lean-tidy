-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force .applicable .congr_assumptions .fsplit .automatic_induction .tidy_attributes .intro_at_least_one
import .monadic_chain
import .smt

import data.list

open tactic

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
  congr_assumptions
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

-- What a pain that we have to do this inside the tactic monad.
meta def check_tactic_list_completes (goals : list expr) (tactics : list (tactic unit)) : tactic unit :=
do
  actual_goals ← get_goals,
  set_goals goals,
  tactics.foldl (λ s t, s >> t) tactic.skip,
  r ← if_then_else tactic.done (pure tt) (pure ff),
  set_goals actual_goals,
  guard r

lemma test : 0 = 0 :=
begin
  success_if_fail { get_goals >>= (λ g, check_tactic_list_completes g []) },
  get_goals >>= (λ g, check_tactic_list_completes [] []),
  simp
end

meta def find_index_tactic_succeeds {α : Type} (f : α → tactic unit) : list α → tactic (option ℕ)
| []     := none
| (h::t) := do
              if_then_else 
                (f h) 
                (pure (some 0)) 
                (do 
                   r ← find_index_tactic_succeeds t,
                   pure (match r with | none := none | some r := some (r + 1) end)
                )

meta def find_unnecessary_hint {α} (goals : list expr ) (tactics : list (tactic α)) (hints: list ℕ) : tactic (option ℕ) :=
find_index_tactic_succeeds
 (λ i, skip)      -- FIXME implement this
 (list.range hints.length)

meta def remove_unnecessary_hint {α} (goals : list expr ) (tactics : list (tactic α)) (hints: list ℕ) : tactic (option (list ℕ)) :=
do o ← find_unnecessary_hint goals tactics hints,
   match o with
   | none     := pure none
   | (some i) := pure (some (hints.remove_nth i))

meta def optimise_hints {α} (goals : list expr) (tactics : list (tactic α)) : list ℕ → tactic (list ℕ)
| hints := do
             o ← remove_unnecessary_hint goals tactics hints,
             match o with
             | none     := (pure hints)
             | (some r) := (optimise_hints r)
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
        let optimised_hints := optimise_hints original_goals numbered_tactics hints in
        trace ("tidy {hints:=" ++ optimised_hints.to_string ++ "}")
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
  tidy
end
