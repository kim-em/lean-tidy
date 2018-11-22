import tidy.rewrite_search.core
import tidy.rewrite_search.module

import .core
import .cm
import .svm

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.metric
open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance

meta def weight.none : ed_weight_constructor :=
  λ α δ, ⟨init_result.pure (), λ g, return table.create⟩

-- TODO I'm ugly
meta def edit_distance_cnst (conf : iconfig.result) (n : option name) := λ α δ,
  let w := match n with
  | some `cm := weight.cm
  | some `svm := weight.svm
  | _ := weight.none
  end in
  @metric.mk α ed_state ed_partial δ (ed_decode conf (w α δ).init) (ed_update (w α δ).calc_weights) ed_init_bound ed_improve_estimate_over

meta def edit_distance (conf : iconfig.result := iconfig.empty_result) (weight : option name := none) : tactic expr :=
  generic_args ``tidy.rewrite_search.metric.edit_distance_cnst [`(conf), `(weight)]

section

iconfig_mk edit_distance
iconfig_add_struct edit_distance tidy.rewrite_search.metric.edit_distance.ed_config

meta def edit_distance_cfg (_ : name) (cfg : iconfig edit_distance) (w : interactive.parse (optional lean.parser.ident)) : cfgtactic unit := do
  cfg ← iconfig.read cfg,
  e ← tactic.to_expr $ ``(edit_distance) (pexpr.of_expr `(cfg)) (pexpr.of_expr `(w)),
  iconfig.publish `metric $ cfgopt.value.pexpr $ pexpr.of_expr e

iconfig_add rewrite_search [ metric.edit_distance : custom edit_distance_cfg ]

end

end tidy.rewrite_search.metric
