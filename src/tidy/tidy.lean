-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .force 
import .backwards_reasoning 
import .forwards_reasoning
import .fsplit 
import .automatic_induction 
import .tidy_attributes 
import .intro_at_least_one
import .chain
import .rewrite_search
import .rewrite_search.tracer
import .injections
import .unfold_aux

universe variables u v

attribute [reducible] cast
-- attribute [reducible] lift_t coe_t coe_b has_coe_to_fun.coe
attribute [reducible] eq.mpr
attribute [ematch] subtype.property

meta def dsimp' := `[dsimp {unfold_reducible := tt, md := semireducible}]
meta def dsimp_all' := `[dsimp at * {unfold_reducible := tt, md := semireducible}]

open tactic

-- TODO split_ifs?
-- TODO refine_struct?

meta def exact_decidable := `[exact dec_trivial]             >> pure "exact dec_trivial"

meta def default_tidy_tactics : list (tactic string) :=
[ force (reflexivity)                         >> pure "refl", 
  exact_decidable,
  propositional_goal >> assumption            >> pure "assumption",
  forwards_reasoning,
  forwards_library_reasoning,
  backwards_reasoning,
  `[ext1]                                     >> pure "ext1",
  intro_at_least_one                          >>= λ ns, pure ("intros " ++ (" ".intercalate ns)),
  automatic_induction,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  fsplit                                      >> pure "fsplit", 
  injections_and_clear                        >> pure "injections_and_clear",
  terminal_goal >> (`[solve_by_elim])         >> pure "solve_by_elim",
  unfold_aux                                  >> pure "unfold_aux",
  -- recover'                                    >> pure "recover'",
  run_tidy_tactics ]

meta structure tidy_cfg extends chain_cfg :=
( trace_result : bool    := ff )
( tactics : list (tactic string) := default_tidy_tactics )

meta def tidy ( cfg : tidy_cfg := {} ) : tactic unit :=
do
  results ← chain cfg.to_chain_cfg cfg.tactics,
  if cfg.trace_result then
    trace ("/- obviously says: -/ " ++ (", ".intercalate results))
  else
    tactic.skip

meta def obviously_tactics : list (tactic string) :=
[ tactic.interactive.rewrite_search_using [`ematch] ] -- TODO should switch this back to search eventually

meta def obviously'  : tactic unit := tidy { tactics := default_tidy_tactics ++ obviously_tactics, trace_result := tt, trace_steps := ff }
meta def obviously_vis  : tactic unit := tidy { tactics := default_tidy_tactics ++ [ tactic.interactive.rewrite_search_using [`ematch] { trace_summary := tt, view := visualiser } ], trace_result := tt, trace_steps := ff }

instance subsingleton_pempty : subsingleton pempty := by tidy
instance subsingleton_punit  : subsingleton punit  := by tidy
