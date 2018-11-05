import tidy.lib.list
import tidy.lib.expr

-- This file almost qualifies for inclusion in the `core` dir, but
-- the hooks into non-core pieces, i.e. providing defaults, and also
-- the external interface it exports is enough to keep it out here.
import .core

-- Default strategy, metric, and tracer used as a fallback by the engine
-- (so must be present)
import .strategy.pexplore
import .metric.edit_distance
import .tracer.unit

open tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

meta def pick_default_tracer   : tactic unit := `[exact tidy.rewrite_search.tracer.unit_tracer]
meta def pick_default_metric   : tactic unit := `[exact tidy.rewrite_search.metric.edit_distance]
meta def pick_default_strategy : tactic unit := `[exact tidy.rewrite_search.strategy.pexplore]

-- This is the "public" config structure which has convenient tactic-mode
-- invocation synatx. The data in this structure is extracted and transformed
-- into the internal representation of the settings and modules by
-- `try_mk_search_instance`.
meta structure rewrite_search_config (α β γ δ : Type) extends rewrite_all_cfg :=
(max_iterations  : ℕ := 500)
(max_discovers   : ℕ := 0)
(suggest         : list name := [])
(optimal         : bool := tt)
(exhaustive      : bool := ff)
(inflate_rws     : bool := ff)
(trace           : bool := ff)
(trace_summary   : bool := ff)
(trace_result    : bool := ff)
(trace_rules     : bool := ff)
(trace_discovery : bool := tt)
(explain_using_conv : bool := tt)
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
    optimal := cfg.optimal,
    exhaustive := cfg.exhaustive,
    trace := cfg.trace,
    trace_summary := cfg.trace_summary,
    trace_rules := cfg.trace_rules,
    trace_result := cfg.trace_result,
    trace_discovery := cfg.trace_discovery,
    explain_using_conv := cfg.explain_using_conv,
    discharger := cfg.discharger,
    simplifier := cfg.simplifier,
    try_simp := cfg.try_simp,
  },
  i ← setup_instance conf strat m tr strat_state metric_state tracer_state prog eqn,
  return i

meta def try_search (cfg : rewrite_search_config α β γ δ) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic (option string) := do
  i ← try_mk_search_instance cfg prog rs eqn,
  match i with
  | none := return none
  | some i := do
    (i, result) ← i.search_until_solved,
    match result with
    | search_result.failure reason := fail reason
    | search_result.success proof steps := do
      exact proof,
      some <$> i.explain proof steps
    end
  end

-- TODO If try_search fails due to a failure to init any of the tracer, metric,
-- or strategy we try again using the "fallback" default versions of all three
-- of these. Instead we could be more thoughtful, and try again only replacing
-- the failing one of these with its respective fallback module version.

meta def rewrite_search_pair (cfg : rewrite_search_config α β γ δ) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic string := do
  result ← try_search cfg prog rs eqn,
  match result with
  | some str := return str
  | none := do
    trace "\nError initialising rewrite_search instance, falling back to emergency config!",
    result ← try_search (mk_fallback_config cfg) prog rs eqn,
    match result with
    | some str := return str
    | none := fail "Could not initialise emergency rewrite_search instance!"
    end
  end

-- TODO: @Keeley: instead of something like
--     `exprs ← close_under_apps exprs`
-- the ideal thing would be to look for lemmas that have a metavariable
-- for their LHS, and try substituting in hypotheses to these.

meta def collect_rw_lemmas (cfg : rewrite_search_config α β γ δ) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic (discovery.progress × list (expr × bool)) := do
  let per := if cfg.help_me then discovery.persistence.try_everything else per,
  (prog, rws) ← discovery.collect use_suggest_annotations per cfg.suggest extra_names,
  hyp_rws ← discovery.rewrite_list_from_hyps,
  let rws := rws ++ extra_rws ++ hyp_rws,

  locs ← local_context,
  rws ← if cfg.inflate_rws then list.join <$> (rws.mmap $ discovery.inflate_rw locs) else pure rws,
  return (prog, rws)

meta def rewrite_search_target (cfg : rewrite_search_config α β γ δ) (try_harder : bool) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string := do
  let cfg := if ¬try_harder then cfg else
    {cfg with max_discovers := max cfg.max_discovers 3, try_simp := tt},

  t ← target,
  if t.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,

  (prog, rws) ← collect_rw_lemmas cfg use_suggest_annotations per extra_names extra_rws,

  (lhs, rhs) ← rw_equation.split t,
  rewrite_search_pair cfg prog rws ⟨lhs, rhs⟩

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def add_expr (s : simp_lemmas) (u : list name) (e : expr) : tactic (simp_lemmas × list name) :=
do
  let e := e.erase_annotations,
  match e with
  | expr.const n _           :=
    (do b ← is_valid_simp_lemma_cnst n, guard b, s ← s.add_simp n, return (s, u))
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), s ← add_simps s eqns, return (s, u))
    <|>
    (do env ← get_env, guard (env.is_projection n).is_some, return (s, n::u))
    <|>
    fail n
  | _ :=
    (do b ← is_valid_simp_lemma e, guard b, s ← s.add e, return (s, u))
    <|>
    fail e
  end

meta def simp_search_target (cfg : rewrite_search_config α β γ δ) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic unit := do
  t ← target,

  (prog, rws) ← collect_rw_lemmas cfg use_suggest_annotations per extra_names extra_rws,

  if cfg.trace_rules then do
    rs_strings ← rws.mmap pp_rule,
    trace ("simp_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
  else skip,

  (s, to_unfold) ← mk_simp_set ff [] [] >>= λ sset, rws.mfoldl (λ c e, add_expr c.1 c.2 e.1 <|> return c) sset,
  (n, pf) ← simplify s to_unfold t {contextual := tt} `eq failed,
  replace_target n pf >> try tactic.triv >> try (tactic.reflexivity reducible)

end tidy.rewrite_search

namespace tactic

open tidy.rewrite_search
open tidy.rewrite_search.discovery.persistence

meta def rewrite_search (cfg : rewrite_search_config α β γ δ . pick_default_config) (try_harder : bool := ff) : tactic string :=
  rewrite_search_target cfg try_harder tt try_everything [] []

meta def rewrite_search_with (rs : list interactive.rw_rule) (cfg : rewrite_search_config α β γ δ . pick_default_config) (try_harder : bool := ff) : tactic string := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs,
  rewrite_search_target cfg try_harder tt speedy [] extra_rws

meta def rewrite_search_using (as : list name) (cfg : rewrite_search_config α β γ δ . pick_default_config) (try_harder : bool := ff) : tactic string := do
  extra_names ← discovery.load_attr_list as,
  rewrite_search_target cfg try_harder ff try_bundles extra_names []

meta def simp_search (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit := do
  simp_search_target cfg tt try_everything [] []

meta def simp_search_with (rs : list interactive.rw_rule) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs,
  simp_search_target cfg tt try_everything [] extra_rws

end tactic
