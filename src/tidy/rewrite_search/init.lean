-- Never import tidy.rewrite_search.engine directly. Go through me.
import .engine

-- Default strategy and tracer used as a fallback by the engine (so mush be present)
import .strategy.edit_distance
import .tracer.unit

open tactic

namespace tidy.rewrite_search

meta def default_tracer := by pick_default_tracer

meta def mk_fallback_config {α β γ : Type} (orig : config α β γ) : config α β unit :=
  { orig with view := default_tracer }

meta def mk_initial_global_state {α β : Type} (strat : strategy α β) : global_state α β :=
⟨ mk_vertex_ref_first, [], [], [], none, strat.init ⟩

meta def setup_instance {α β γ : Type} (conf : config α β γ) (tracer_state : γ) (rs : list (expr × bool)) (lhs rhs : expr) : tactic (inst α β γ) := do
  let i := inst.mk conf rs (mk_initial_global_state conf.strategy) tracer_state,
  (i, vl) ← i.add_root_vertex lhs side.L,
  (i, vr) ← i.add_root_vertex rhs side.R,
  i ← i.add_pair vl vr,
  return i

meta def try_mk_search_instance {α β γ : Type} (conf : config α β γ) (rs : list (expr × bool)) (lhs rhs : expr) : tactic (option (inst α β γ)) :=
do
  tracer_state ← conf.view.init,
  match tracer_state with
  | init_result.failure α reason := do
    trace ("Warning: failed to initialise tracer! Reason:\n" ++ reason),
    return none
  | init_result.success tracer_state := do
    i ← setup_instance conf tracer_state rs lhs rhs,
    return (some i)
  end

end tidy.rewrite_search