import tidy.rewrite_search.engine
import tidy.lib

import system.io

open tidy.rewrite_search

namespace tidy.rewrite_search.tracer.graph

open tactic
open io.process.stdio

def SUCCESS_CHAR : string := "S"
def ERROR_CHAR   : string := "E"
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

inductive spawn_result
| success : io.proc.child → spawn_result -- Client launched and the client reported success status
| abort : string → spawn_result          -- Client launched and we got a bad response code
| failure                                -- Could not launch client
| missing                                -- The script we tried to launch does't exist

meta def read_until_nl (h : io.handle) : io string := do
  c ← io.fs.read h 1,
  match c.to_list with
  | ['\n'] := return ""
  | [c]    := do r ← read_until_nl, return (c.to_string ++ r)
  | _      := return ""
  end

meta def try_launch_with_path (path : string) : io spawn_result := do
  ex ← file_exists (get_app_path path "client"),
  if ex then do
    c ← io.proc.spawn (args path "client"),
    buff ← io.fs.read c.stdout 1,
    str ← pure (buff.to_string),
    if str = SUCCESS_CHAR then
      return (spawn_result.success c)
    else if str = ERROR_CHAR then do
      reason ← read_until_nl c.stdout,
      return (spawn_result.abort reason)
    else if str = "" then
      return spawn_result.failure
    else
      return (spawn_result.abort (format!"bug: unknown client status character \"{str}\"").to_string)
  else
    return spawn_result.missing

meta def try_launch_with_paths : list string → io spawn_result
| []          := return spawn_result.failure
| (p :: rest) := do
  sr ← try_launch_with_path p,
  match sr with
  | spawn_result.missing := try_launch_with_paths rest
  | _                    := return sr
  end

meta def diagnose_launch_failure : io string := do
  c ← io.proc.spawn { cmd := "python3", args := ["--version"], stdin := piped, stdout := piped, stderr := piped },
  r ← io.proc.wait c,
  match r with
  | 255 := return "python3 is missing, and the graph visualiser requires it. Please install python3."
  | 0   := return "bug: python3 present but could not launch client!"
  | ret := return (format!"bug: unexpected return code {ret} during launch failure diagnosis").to_string
  end

open tidy.rewrite_search.init_result

meta def graph_tracer_init : tactic (init_result visualiser) := do
  c ← tactic.unsafe_run_io (try_launch_with_paths SEARCH_PATHS),
  match c with
  | spawn_result.success c    := let vs : visualiser := ⟨ c ⟩ in do vs.publish "S\n", return (success vs)
  | spawn_result.abort reason := return (failure visualiser ("Error! " ++ reason))
  | spawn_result.failure      := do
    reason ← tactic.unsafe_run_io diagnose_launch_failure,
    return (failure visualiser ("Error! " ++ reason))
  | spawn_result.missing      := return (failure visualiser ("Error! bug: could not determine client location"))
  end

meta def graph_tracer_publish_vertex (vs : visualiser) (v : vertex) : tactic unit := do
  vs.publish (to_string (format!"V|{v.id.to_string}|{v.s.to_string}|{v.pp}"))

meta def graph_tracer_publish_edge (vs : visualiser) (e : edge) : tactic unit :=
  vs.publish (to_string (format!"E|{e.f.to_string}|{e.t.to_string}"))

meta def graph_tracer_publish_pair (vs : visualiser) (l r : table_ref) : tactic unit :=
  vs.publish (to_string (format!"P|{l.to_string}|{r.to_string}"))

meta def graph_tracer_publish_visited (vs : visualiser) (v : vertex) : tactic unit :=
  vs.publish (to_string (format!"B|{v.id.to_string}"))

meta def graph_tracer_publish_finished (vs : visualiser) (es : list edge) : tactic unit := do
  es.mmap' (λ e : edge, vs.publish (to_string (format!"F|{e.f.to_string}|{e.t.to_string}"))),
  vs.publish (to_string (format!"D"))

meta def graph_tracer_dump (vs : visualiser) (str : string) : tactic unit :=
  vs.publish (str ++ "\n")

meta def graph_tracer_pause (vs : visualiser) : tactic unit :=
  vs.pause

end tidy.rewrite_search.tracer.graph

namespace tidy.rewrite_search.tracer

open tidy.rewrite_search.tracer.graph

meta def graph_tracer : tracer_constructor visualiser := λ α β γ,
  tracer.mk α β γ graph_tracer_init graph_tracer_publish_vertex graph_tracer_publish_edge
    graph_tracer_publish_pair graph_tracer_publish_visited graph_tracer_publish_finished graph_tracer_dump graph_tracer_pause

end tidy.rewrite_search.tracer