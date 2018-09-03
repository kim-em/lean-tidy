import tidy.rewrite_search.engine

open tidy.rewrite_search

namespace tidy.rewrite_search.tracer.unit

open tactic

meta def unit_tracer_init : tactic (init_result unit) := return (init_result.success ())
meta def unit_tracer_publish_vertex (_ : unit) (_ : vertex) : tactic unit := skip
meta def unit_tracer_publish_edge (_ : unit) (_ : edge) : tactic unit := skip
meta def unit_tracer_publish_pair (_ : unit) (_ _ : table_ref) : tactic unit := skip
meta def unit_tracer_publish_visited (_ : unit) (_ : vertex) : tactic unit := skip
meta def unit_tracer_publish_finished (_ : unit) (_ : list edge) : tactic unit := skip
meta def unit_tracer_dump (_ : unit) (_ : string) : tactic unit := skip
meta def unit_tracer_pause (_ : unit) : tactic unit := skip

end tidy.rewrite_search.tracer.unit

namespace tidy.rewrite_search.tracer

open tidy.rewrite_search.tracer.unit

meta def unit_tracer : tracer unit :=
  ⟨ unit_tracer_init, unit_tracer_publish_vertex, unit_tracer_publish_edge, unit_tracer_publish_pair,
    unit_tracer_publish_visited, unit_tracer_publish_finished, unit_tracer_dump, unit_tracer_pause ⟩

end tidy.rewrite_search.tracer