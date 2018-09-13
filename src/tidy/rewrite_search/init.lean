import .core

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
(max_iterations  : ℕ := 500)
(max_discovers   : ℕ := 3)
(suggest         : list name := [])
(trace           : bool := ff)
(trace_summary   : bool := ff)
(trace_result    : bool := ff)
(trace_rules     : bool := ff)
(trace_discovery : bool := tt)
(exhaustive      : bool := ff)
(help_me         : bool := ff)
(metric          : metric_constructor β γ . pick_default_metric)
(strategy        : strategy_constructor α . pick_default_strategy)
(view            : tracer_constructor δ   . pick_default_tracer)

-- TODO coerce {} = ∅ into default_config?

open tidy.rewrite_search.edit_distance
open tidy.rewrite_search.metric.edit_distance
open tidy.rewrite_search.strategy.pexplore
open discovery.persistence

meta def default_config : rewrite_search_config pexplore_state ed_state ed_partial unit := {}
meta def pick_default_config : tactic unit := `[exact tidy.rewrite_search.default_config]

variables {α β γ δ : Type}

meta def mk_fallback_config (orig : rewrite_search_config α β γ δ) : rewrite_search_config pexplore_state ed_state ed_partial unit :=
  {orig with view := begin pick_default_tracer end,
             metric := begin pick_default_metric end,
             strategy := begin pick_default_strategy end}

meta def mk_initial_search_state (conf : config) (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ) (strat_state : α) (metric_state : β) (tr_state : δ) (prog : discovery.progress) : search_state α β γ δ :=
⟨tr, conf, strat_state, metric_state, table.create, table.create, table.create, none, tr_state, prog, statistics.init⟩

meta def setup_instance (conf : config) (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ) (s_state : α) (m_state : β) (tr_state : δ) (prog : discovery.progress) (eqn : sided_pair expr) : tactic (inst α β γ δ) := do
  let g := mk_initial_search_state conf s m tr s_state m_state tr_state prog,
  (g, vl) ← g.add_root_vertex eqn.l side.L,
  (g, vr) ← g.add_root_vertex eqn.r side.R,
  g ← s.startup g m vl vr,
  return ⟨m, s, g⟩

meta def instantiate_modules (cfg : rewrite_search_config α β γ δ) : strategy α β γ δ × metric α β γ δ × tracer α β γ δ :=
(cfg.strategy β γ δ, cfg.metric α δ, cfg.view α β γ)

meta def try_mk_search_instance (cfg : rewrite_search_config α β γ δ) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic (option (inst α β γ δ)) :=
do
  let (strat, m, tr) := instantiate_modules cfg,
  init_result.try "tracer"   tr.init    $ λ tracer_state,
  init_result.try "metric"   m.init     $ λ metric_state,
  init_result.try "strategy" strat.init $ λ strat_state,
  do
  let conf : config := {
    rs := rs,
    max_iterations := cfg.max_iterations,
    max_discovers := cfg.max_discovers,
    trace := cfg.trace,
    trace_summary := cfg.trace_summary,
    trace_result := cfg.trace_result,
    trace_discovery := cfg.trace_discovery,
    exhaustive := cfg.exhaustive,
    discharger := cfg.discharger,
    simplifier := cfg.simplifier
  },
  i ← setup_instance conf strat m tr strat_state metric_state tracer_state prog eqn,
  return i

end tidy.rewrite_search