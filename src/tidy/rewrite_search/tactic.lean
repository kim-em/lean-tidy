import tidy.lib.list
import tidy.lib.expr

-- This file almost qualifies for inclusion in the `core` dir, but
-- the hooks into non-core pieces, i.e. providing defaults, and also
-- the external interface it exports is enough to keep it out here.
import .core
import .module

-- Default strategy, metric, and tracer used as a fallback by the engine
-- (so must be present)
import .strategy.pexplore
import .metric.edit_distance
import .tracer.unit

import tactic.iconfig

open tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

meta def default_strategy : expr ff := expr.const `pexplore []
meta def default_metric   : expr ff := expr.const `edit_distance []
meta def default_tracer   : expr ff := expr.const `unit []

-- Another thing is that we can use our super great config system
-- when invoking `iconfig_xxx` commands, by just setting up the original
-- ennvironment.

-- Then, we will finally be able to do the fail-one-at-a-time
-- thing too.

open discovery.persistence

meta def mk_initial_search_state (conf : config) (try_simp : bool) (rs : list (expr × bool)) (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ) (strat_state : α) (metric_state : β) (tr_state : δ) (prog : discovery.progress) : search_state α β γ δ :=
⟨tr, conf, {try_simp := try_simp}, rs, strat_state, metric_state, table.create, table.create, table.create, none, tr_state, prog, statistics.init⟩

meta def mk_instance (conf : config) (try_simp : bool) (rs : list (expr × bool)) (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ) (s_state : α) (m_state : β) (tr_state : δ) (prog : discovery.progress) (eqn : sided_pair expr) : tactic (packet inst) := do
  i ← tactic.up (do
    let g := mk_initial_search_state conf try_simp rs s m tr s_state m_state tr_state prog,
    (g, vl) ← g.add_root_vertex eqn.l side.L,
    (g, vr) ← g.add_root_vertex eqn.r side.R,
    g ← s.startup g m vl vr,
    pure (⟨m, s, g⟩ : inst α β γ δ)
  ),
  return ⟨⟨α, β, γ, δ⟩, i.down⟩

meta def try_mk_search_instance (cfg : iconfig.result) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic (option (packet inst)) := do
  ulift.up conf ← tactic.up $ cfg.struct `tidy.rewrite_search.config tidy.rewrite_search.config,
  stack ← instantiate_modules
    (cfg.ipexpr `strategy default_strategy)
    (cfg.ipexpr `metric   default_metric)
    (cfg.ipexpr `tracer   default_tracer),

  init_result.try "strategy" stack.st.init $ λ strat_state,
  init_result.try "metric"   stack.mt.init $ λ metric_state,
  init_result.try "tracer"   stack.tr.init $ λ tracer_state, do
  option.some <$>
    mk_instance conf (cfg.ibool `try_simp ff) rs stack.st stack.mt stack.tr strat_state metric_state tracer_state prog eqn

meta def try_search (cfg : iconfig.result) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic (option string) := tactic.down $ do
  i ← try_mk_search_instance cfg prog rs eqn,
  tactic.up $ match i with
  | none := return none
  | some i := do
    (i, result) ← i.v.search_until_solved,
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

meta def mk_fallback_config (cfg : iconfig.result) : iconfig.result :=
  let cfg := cfg.clear `strategy in
  let cfg := cfg.clear `metric in
  let cfg := cfg.clear `tracer in
  cfg

meta def rewrite_search_pair (cfg : iconfig.result) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic string := do
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

meta def collect_rw_lemmas (cfg : collect_config) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic (discovery.progress × list (expr × bool)) := do
  let per := if cfg.help_me then discovery.persistence.try_everything else per,
  (prog, rws) ← discovery.collect use_suggest_annotations per cfg.suggest extra_names,
  hyp_rws ← discovery.rewrite_list_from_hyps,
  let rws := rws ++ extra_rws ++ hyp_rws,

  locs ← local_context,
  rws ← if cfg.inflate_rws then list.join <$> (rws.mmap $ discovery.inflate_rw locs)
        else pure rws,
  return (prog, rws)

meta def rewrite_search_target (cfg : iconfig rewrite_search) (try_harder : bool) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string := do
  cfg ← iconfig.read cfg,
  let cfg := if ¬try_harder then cfg
             else cfg.setl [
               (`try_simp, cfgopt.value.bool tt),
               (`max_discovers, cfgopt.value.nat $ max 3 $ cfg.inat `max_discovers 3)
             ],
  t ← target,
  if t.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,

  collect_cfg ← cfg.struct `tidy.rewrite_search.collect_config tidy.rewrite_search.collect_config,
  (prog, rws) ← collect_rw_lemmas collect_cfg use_suggest_annotations per extra_names extra_rws,

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

meta def simp_search_target (cfg : iconfig rewrite_search) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic unit := do
  t ← target,
  cfg ← iconfig.read cfg,

  collect_cfg ← cfg.struct `collect_config collect_config,
  (prog, rws) ← collect_rw_lemmas collect_cfg use_suggest_annotations per extra_names extra_rws,

  if cfg.ibool `trace_rules ff then do
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

meta def rewrite_search (cfg : iconfig rewrite_search) (try_harder : bool := ff) : tactic string :=
  rewrite_search_target cfg try_harder tt try_everything [] []

meta def rewrite_search_with (rs : list interactive.rw_rule) (cfg : iconfig rewrite_search) (try_harder : bool := ff) : tactic string := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs,
  rewrite_search_target cfg try_harder tt speedy [] extra_rws

meta def rewrite_search_using (as : list name) (cfg : iconfig rewrite_search) (try_harder : bool := ff) : tactic string := do
  extra_names ← discovery.load_attr_list as,
  rewrite_search_target cfg try_harder ff try_bundles extra_names []

meta def simp_search (cfg : iconfig rewrite_search) : tactic unit := do
  simp_search_target cfg tt try_everything [] []

meta def simp_search_with (rs : list interactive.rw_rule) (cfg : iconfig rewrite_search) : tactic unit := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs,
  simp_search_target cfg tt try_everything [] extra_rws

end tactic
