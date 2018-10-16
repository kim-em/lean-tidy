-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

import .init
import .discovery

import tidy.lib.list
import tidy.lib.expr

open tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

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

-- TODO If try_search fails due to a failure to init any of the tracer, metric, or strategy we try again
-- using the "fallback" default versions of all three of these. Instead we could be more thoughtful,
-- and try again only replacing the failing one of these with its respective fallback module version.

meta def collect_rw_lemmas (cfg : rewrite_search_config α β γ δ) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic (discovery.progress × list (expr × bool)) := do
  let per := if cfg.help_me then discovery.persistence.try_everything else per,
  (prog, rws) ← discovery.collect use_suggest_annotations per cfg.suggest extra_names,
  hyp_rws ← discovery.rewrite_list_from_hyps,
  let rws := rws ++ extra_rws ++ hyp_rws,

  locs ← local_context,
  rws ← if cfg.inflate_rws then list.join <$> (rws.mmap $ discovery.inflate_rw locs) else pure rws,
  return (prog, rws)

meta def rewrite_search_target (cfg : rewrite_search_config α β γ δ) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string := do
  t ← target,
  if t.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,

  (prog, rws) ← collect_rw_lemmas cfg use_suggest_annotations per extra_names extra_rws,

  if cfg.trace_rules then
    do rs_strings ← pp_rules rws,
      trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
  else skip,

  match t with
  | `(%%lhs = %%rhs) := rewrite_search_pair cfg prog rws ⟨lhs, rhs⟩
  | `(%%lhs ↔ %%rhs) := rewrite_search_pair cfg prog rws ⟨lhs, rhs⟩
  | _                := fail "target is not an equation or iff"
  end

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

  if cfg.trace_rules then
    do rs_strings ← pp_rules rws,
      trace ("simp_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
  else skip,

  (s, to_unfold) ← mk_simp_set ff [] [] >>= λ sset, rws.mfoldl (λ c e, add_expr c.1 c.2 e.1 <|> return c) sset,
  (n, pf) ← simplify s to_unfold t {contextual := tt} `eq failed,
  replace_target n pf >> try tactic.triv >> try (tactic.reflexivity reducible)

end tidy.rewrite_search

namespace tactic.interactive

open interactive
open tidy.rewrite_search tidy.rewrite_search.discovery.persistence

meta def rewrite_search (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string :=
  rewrite_search_target cfg tt try_everything [] []

meta def rewrite_search_with (rs : parse rw_rules) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs.rules,
  rewrite_search_target cfg tt speedy [] extra_rws

meta def rewrite_search_using (as : list name) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  extra_names ← discovery.load_attr_list as,
  rewrite_search_target cfg ff try_bundles extra_names []

-- @Scott should we still do this?
--  exprs ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas

-- @Keeley, the ideal thing would be to look for lemmas that have a metavariable for their LHS,
-- and try substituting in hypotheses to these.

meta def simp_search (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit := do
  simp_search_target cfg tt try_everything [] []

meta def simp_search_with (rs : parse rw_rules) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic unit := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs.rules,
  simp_search_target cfg tt try_everything [] extra_rws

end tactic.interactive
