import tactic.iconfig
import tidy.rewrite_search.core
import tidy.rewrite_search.module

open tidy.rewrite_search

namespace tidy.rewrite_search.tracer.unit

open tactic

meta def unit_tracer_init : tactic (init_result unit) := init_result.pure ()
meta def unit_tracer_publish_vertex (_ : unit) (_ : vertex) : tactic unit := skip
meta def unit_tracer_publish_edge (_ : unit) (_ : edge) : tactic unit := skip
meta def unit_tracer_publish_visited (_ : unit) (_ : vertex) : tactic unit := skip
meta def unit_tracer_publish_finished (_ : unit) (_ : list edge) : tactic unit := skip
meta def unit_tracer_dump (_ : unit) (_ : string) : tactic unit := skip
meta def unit_tracer_pause (_ : unit) : tactic unit := skip

end tidy.rewrite_search.tracer.unit

namespace tidy.rewrite_search.tracer

open tidy.rewrite_search.tracer.unit

meta def no_cfg (_ : name) (_ : interactive.parse interactive.types.texpr) : cfgtactic unit := tactic.skip

iconfig_add rewrite_search [ no : custom no_cfg ]

meta def unit_cnst := λ α β γ,
  tracer.mk α β γ unit_tracer_init unit_tracer_publish_vertex unit_tracer_publish_edge unit_tracer_publish_visited unit_tracer_publish_finished unit_tracer_dump unit_tracer_pause

meta def unit : tactic expr :=
  generic `tidy.rewrite_search.tracer.unit_cnst

meta def unit_cfg (_ : name) : cfgtactic _root_.unit :=
  iconfig.publish `tracer $ cfgopt.value.pexpr $ expr.const `unit []

iconfig_add rewrite_search [ tracer.unit : custom unit_cfg ]

end tidy.rewrite_search.tracer
