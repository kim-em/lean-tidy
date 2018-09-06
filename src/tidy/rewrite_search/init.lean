-- Never import tidy.rewrite_search.engine directly. Go through me.
import .engine

-- Default strategy, metric, and tracer used as a fallback by the engine (so mush be present)
import .strategy.pexplore
import .metric.edit_distance
import .tracer.unit

open tactic

namespace tidy.rewrite_search

meta def pick_default_tracer   : tactic unit := `[exact tidy.rewrite_search.tracer.unit_tracer]
meta def pick_default_metric   : tactic unit := `[exact tidy.rewrite_search.metric.edit_distance]
meta def pick_default_strategy : tactic unit := `[exact tidy.rewrite_search.strategy.pexplore]

-- This is the "public" config structure which has convenient tactic-mode invocation synatx.
-- The data in this structure is extracted and transformed into the internal representation
-- of the settings and modules by `try_mk_search_instance`.
meta structure rewrite_search_config (α β γ δ : Type) extends rewrite_all_cfg :=
(trace         : bool := ff)
(trace_summary : bool := ff)
(trace_result  : bool := ff)
(exhaustive    : bool := ff)
(metric        : metric_constructor β γ . pick_default_metric)
(strategy      : strategy_constructor α . pick_default_strategy)
(view          : tracer_constructor δ   . pick_default_tracer)

-- TODO coerce {} = ∅ into default_config?

open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance
open tidy.rewrite_search.strategy.pexplore

meta def default_config : rewrite_search_config pexplore_state ed_state ed_partial unit := {}
meta def pick_default_config : tactic unit := `[exact tidy.rewrite_search.default_config]

variables {α β γ δ : Type}

--TODO make a more robust "fallback_config" (vs "default_config")?
meta def mk_fallback_config (orig : rewrite_search_config α β γ δ) :=
  default_config

meta def mk_initial_search_state (conf : config) (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ) (tr_state : δ) : search_state α β γ δ :=
⟨tr, conf, s.init, m.init, table.create, table.create, table.create, none, tr_state⟩

meta def setup_instance (conf : config) (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ) (tr_state : δ) (lhs rhs : expr) : tactic (inst α β γ δ) := do
  let g := mk_initial_search_state conf s m tr tr_state,
  (g, vl) ← g.add_root_vertex lhs side.L,
  (g, vr) ← g.add_root_vertex rhs side.R,
  g ← s.startup g m vl vr,
  return ⟨m, s, g⟩

meta def instantiate_modules (cfg : rewrite_search_config α β γ δ) : strategy α β γ δ × metric α β γ δ × tracer α β γ δ :=
(cfg.strategy β γ δ, cfg.metric α δ, cfg.view α β γ)

meta def try_mk_search_instance (cfg : rewrite_search_config α β γ δ) (rs : list (expr × bool)) (lhs rhs : expr) : tactic (option (inst α β γ δ)) :=
do
  let (strat, m, tr) := instantiate_modules cfg,
  tracer_state ← tr.init,
  match tracer_state with
  | init_result.failure α reason := do
    trace ("Warning: failed to initialise tracer! Reason:\n" ++ reason),
    return none
  | init_result.success tracer_state := do
    let conf : config := {
      rs := rs,
      trace := cfg.trace,
      trace_summary := cfg.trace_summary,
      trace_result := cfg.trace_result,
      exhaustive := cfg.exhaustive,
      discharger := cfg.discharger,
      simplifier := cfg.simplifier
    },
    i ← setup_instance conf strat m tr tracer_state lhs rhs,
    return (some i)
  end

end tidy.rewrite_search