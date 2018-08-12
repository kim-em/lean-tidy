import tidy.rewrite_search.engine

import tactic.debug

namespace tidy.rewrite_search

open tactic

meta def graph_tracer_init : tactic debug.handle :=
  debug.mk_handle "rewrite_search.socket"

meta def graph_tracer_publish_vertex (h : debug.handle) (v : vertex) : tactic unit := do
  let sn := match v.s with
    | none   := "?"
    | some s := s.to_string
  end,
  h.publish (to_string (format!"V|{v.id.to_string}|{sn}|{v.pp}\n"))

meta def graph_tracer_publish_edge (h : debug.handle) (e : edge) : tactic unit :=
  h.publish (to_string (format!"E|{e.f.to_string}|{e.t.to_string}\n"))

meta def graph_tracer_publish_pair (h : debug.handle) (l r : vertex_ref) : tactic unit :=
  h.publish (to_string (format!"P|{l.to_string}|{r.to_string}\n"))

meta def graph_tracer_publish_finished (h : debug.handle) : tactic unit :=
  h.publish "D\n"

meta def graph_tracer_dump (h : debug.handle) (str : string) : tactic unit :=
  h.publish (str ++ "\n")

meta def graph_tracer_pause (h : debug.handle) : tactic unit :=
  h.pause

meta def graph_tracer : tracer debug.handle :=
  ⟨ graph_tracer_init, graph_tracer_publish_vertex, graph_tracer_publish_edge,
    graph_tracer_publish_pair, graph_tracer_publish_finished, graph_tracer_dump,
    graph_tracer_pause ⟩

end tidy.rewrite_search