-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic.basic
import tactic.tidy
import .backwards_reasoning
import .forwards_reasoning
import .rewrite_search
import .rewrite_search.tracer
import .luxembourg_chain
import category_theory.category

open tactic

meta def extended_tidy_tactics : list (tactic string) :=
[ reflexivity                                 >> pure "refl",
  `[exact dec_trivial]                        >> pure "exact dec_trivial",
  propositional_goal >> assumption            >> pure "assumption",
  backwards_reasoning,
  `[ext1]                                     >> pure "ext1",
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  auto_cases,
  `[apply_auto_param]                         >> pure "apply_auto_param",
  `[dsimp at *]                               >> pure "dsimp at *",
  `[simp at *]                                >> pure "simp at *",
  fsplit                                      >> pure "fsplit",
  injections_and_clear                        >> pure "injections_and_clear",
  terminal_goal >> (`[solve_by_elim])         >> pure "solve_by_elim",
  forwards_reasoning,
  propositional_goal >> forwards_library_reasoning,
  `[unfold_aux]                               >> pure "unfold_aux",
  tactic.interactive.rewrite_search_using [`search],
  tidy.run_tactics ]

@[obviously] meta def obviously_1 := tidy { tactics := extended_tidy_tactics }