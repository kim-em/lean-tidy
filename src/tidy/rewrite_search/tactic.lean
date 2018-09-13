-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

import .init
import .discovery

import tidy.lib.list

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

meta def rewrite_search_pair (cfg : rewrite_search_config α β γ δ) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) := do
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

meta def rewrite_search_target (cfg : rewrite_search_config α β γ δ) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string := do
  t ← target,
  if t.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,

  let per := if cfg.help_me then discovery.persistence.try_everything else per,
  (prog, rws) ← discovery.collect use_suggest_annotations per cfg.suggest extra_names,
  let rws := rws ++ extra_rws,

  if cfg.trace_rules then
    do rs_strings ← pp_rules rws,
      trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
  else skip,

  match t with
  | `(%%lhs = %%rhs) := rewrite_search_pair cfg prog rws ⟨lhs, rhs⟩
  | `(%%lhs ↔ %%rhs) := rewrite_search_pair cfg prog rws ⟨lhs, rhs⟩
  | _                := fail "target is not an equation or iff"
  end

end tidy.rewrite_search

namespace tactic.interactive

open interactive
open tidy.rewrite_search tidy.rewrite_search.discovery.persistence

meta def rewrite_search (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string :=
  rewrite_search_target cfg tt try_everything [] []

meta def rewrite_search_using (as : list name) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  extra_names ← discovery.load_attr_list as,
  rewrite_search_target cfg ff try_bundles extra_names []

meta def rewrite_search_with (rs : parse rw_rules) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  extra_rws ← discovery.rewrite_list_from_rw_rules rs,
  rewrite_search_target cfg ff speedy [] extra_rws

-- @Scott should we still do this?
--  exprs ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas

end tactic.interactive
