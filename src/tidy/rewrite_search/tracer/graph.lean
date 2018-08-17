import tidy.rewrite_search.engine
import tidy.lib

import system.io

namespace tidy.rewrite_search

open tactic
open io.process.stdio

def LAUNCH_CHAR : string := "S"
def SEARCH_PATHS : list string := [
  "_target/deps/lean-tidy/res/graph_tracer",
  "res/graph_tracer"
]

def get_app_path (dir : string) (app : string) : string := dir ++ "/" ++ app ++ ".py"

def args (dir : string) (app : string) : io.process.spawn_args := {
  cmd    := "python3",
  args   := [get_app_path dir app],
  stdin  := piped,
  stdout := piped,
  stderr := inherit,
  env    := [
    ("PYTHONPATH", some (dir ++ "/pygraphvis.zip/pygraphvis")),
    ("PYTHONIOENCODING", "utf-8")
  ],
}

structure visualiser :=
  (proc : io.proc.child)
meta def visualiser.publish (v : visualiser) (s : string) : tactic unit :=
  let chrs : list char := (s.to_list.stripl ['\n', '\x0D']).append ['\n'] in
  tactic.unsafe_run_io (io.fs.write v.proc.stdin (char_buffer.from_list (utf8decode chrs)))
meta def visualiser.pause (v : visualiser) : tactic unit :=
  tactic.unsafe_run_io (do io.fs.read v.proc.stdout 1, return ())

def file_exists (path : string) : io bool := do
  c ← io.proc.spawn { cmd := "test", args := ["-f", path] },
  retval ← io.proc.wait c,
  return (retval = 0)

meta def try_launch_with_path (path : string) : io (option io.proc.child) := do
  ex ← file_exists (get_app_path path "client"),
  if ex then do
    c ← io.proc.spawn (args path "client"),
    buff ← io.fs.read c.stdout 1,
    str ← pure (buff.to_string),
    return (if str = LAUNCH_CHAR then c else none)
  else
    return none

meta def try_launch_with_paths : list string → io (option io.proc.child)
| []          := return none
| (p :: rest) := do
  c ← try_launch_with_path p,
  match c with
  | none   := try_launch_with_paths rest
  | some c := return c
  end

meta def graph_tracer_init : tactic visualiser := do
  c ← tactic.unsafe_run_io (try_launch_with_paths SEARCH_PATHS),
  match c with
  | none   := fail "could not open child"
  | some c := let vs : visualiser := ⟨ c ⟩ in do vs.publish "D\n", return vs
  end

meta def graph_tracer_publish_vertex (vs : visualiser) (v : vertex) : tactic unit := do
  let sn := match v.s with
    | none   := "?"
    | some s := s.to_string
  end,
  vs.publish (to_string (format!"V|{v.id.to_string}|{sn}|{v.pp}\n"))

meta def graph_tracer_publish_edge (vs : visualiser) (e : edge) : tactic unit :=
  vs.publish (to_string (format!"E|{e.f.to_string}|{e.t.to_string}\n"))

meta def graph_tracer_publish_pair (vs : visualiser) (l r : vertex_ref) : tactic unit :=
  vs.publish (to_string (format!"P|{l.to_string}|{r.to_string}\n"))

meta def graph_tracer_publish_finished (vs : visualiser) (es : list edge) : tactic unit :=
  es.mmap' (λ e : edge, vs.publish (to_string (format!"F|{e.f.to_string}|{e.t.to_string}\n")))

meta def graph_tracer_dump (vs : visualiser) (str : string) : tactic unit :=
  vs.publish (str ++ "\n")

meta def graph_tracer_pause (vs : visualiser) : tactic unit :=
  vs.pause

meta def graph_tracer : tracer visualiser :=
  ⟨ graph_tracer_init, graph_tracer_publish_vertex, graph_tracer_publish_edge,
    graph_tracer_publish_pair, graph_tracer_publish_finished, graph_tracer_dump,
    graph_tracer_pause ⟩

end tidy.rewrite_search