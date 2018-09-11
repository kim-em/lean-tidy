-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

import .init
import .discovery

import tidy.lib.list

open interactive interactive.types expr tactic

variables {α β γ δ : Type}

namespace tidy.rewrite_search

def how.to_tactic (rule_strings : list string) : how → option string
| (how.rewrite index s location) := some ("nth_rewrite" ++ (match s with | side.L := "_lhs" | side.R := "_rhs" end) ++ " " ++ to_string location ++ " " ++ (rule_strings.nth index).iget)
| _ := none

meta def explain_proof (rule_strings : list string) (steps : list how) : string :=
string.intercalate ",\n" (steps.map $ λ s : how, (s.to_tactic rule_strings).to_list).join

def how.concisely (rule_strings : list string) : how → option string
| (how.rewrite index side location) := some (rule_strings.nth index).iget
| _ := none

meta def explain_proof_concisely (rule_strings : list string) (steps : list how) (needs_refl : bool) : string :=
"erw [" ++ (string.intercalate ", " (steps.map $ λ s : how, (s.concisely rule_strings).to_list).join) ++ "]" ++ (if needs_refl then ", refl" else "")

-- fails if we can't just use rewrite
-- otherwise, returns 'tt' if we need a `refl` at the end
meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) : tactic bool :=
lock_tactic_state $
focus1 $
do
  t ← target,
  rewrites.mmap' (λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}),
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

meta def pp_rules (rs : list (expr × bool)) : tactic (list string) := rs.mmap (λ p, (do pp ← pretty_print p.1, return (if p.2 then ("←" ++ pp) else pp)))

meta def handle_search_result (cfg : rewrite_search_config α β γ δ) (rules : list (expr × bool)) (result : search_result) : tactic string := do
match result with
| search_result.failure reason      := fail reason
| search_result.success proof steps := do
    if cfg.trace then do
      pp ← pretty_print proof,
      trace format!"rewrite_search found proof:\n{pp}"
    else skip,
    rules_strings ← pp_rules rules,
    explanation ← (do
      let rewrites := (steps.map $ λ s, match s with
                                   | how.rewrite index _ _ := [(rules.nth index).iget]
                                   | _ := []
                                   end).join,
      needs_refl ← check_if_simple_rewrite_succeeds rewrites,
      return (explain_proof_concisely rules_strings steps needs_refl)) <|> return (explain_proof rules_strings steps),
    if cfg.trace_result then trace explanation
    else skip,
    exact proof,
    return explanation
end

meta def try_search (cfg : rewrite_search_config α β γ δ) (rs : list (expr × bool)) (lhs rhs : expr) : tactic (option string) := do
  i ← try_mk_search_instance cfg rs lhs rhs,
  match i with
  | none := return none
  | some i := do
    result ← i.search_until_solved,
    str ←  handle_search_result cfg rs result,
    return str
  end

meta def run_rewrite_search (cfg : rewrite_search_config α β γ δ) (rs : list (expr × bool)) (lhs rhs : expr) := do
  result ← try_search cfg rs lhs rhs,
  match result with
  | some str := return str
  | none := do
    trace "\nError initialising rewrite_search instance, falling back to emergency config!",
    result ← try_search (mk_fallback_config cfg) rs lhs rhs,
    match result with
    | some str := return str
    | none := fail "Could not initialise emergency rewrite_search instance!"
    end
  end

-- TODO If try_search fails due to a failure to init any of the tracer, metric, or strategy we try again
-- using the "fallback" default versions of all three of these. Instead we could be more thoughtful,
-- and try again only replacing the failing one of these with its respective fallback module version.

meta def do_rewrite_search (cfg : rewrite_search_config α β γ δ) (rs : list (expr × bool)) : tactic string := do
  if cfg.trace_rules then
    do rs_strings ← pp_rules rs,
      trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
  else skip,

  t ← target,
  match t with
  | `(%%lhs = %%rhs) := run_rewrite_search cfg rs lhs rhs
  | `(%%lhs ↔ %%rhs) := run_rewrite_search cfg rs lhs rhs
  | _                := fail "target is not an equation or iff"
  end

meta def is_acceptable_rewrite (r : expr) : tactic bool := do
  t ← infer_type r,
  return $ is_eq_after_binders t ∨ is_iff_after_binders t

meta def mk_complete_rewrite_list (l : list expr) : list (expr × bool) :=
  l.map (λ e, (e, ff)) ++ l.map (λ e, (e, tt))

meta def load_attr_list : list name → tactic (list name)
| [] := return []
| (a :: rest) := do
  names ← attribute.get_instances a,
  l ← load_attr_list rest,
  return $ names ++ l

meta def load_names (l : list name) : tactic (list expr) :=
  l.mmap mk_const

meta def check_target : tactic unit := do
  tgt ← target,
  if tgt.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip

end tidy.rewrite_search

namespace tactic.interactive

open tidy.rewrite_search

meta def rewrite_search (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  check_target,
  sugg_b ← discovery.get_suggestions,
  conf_b ← cfg.suggest.mmap discovery.get_bundle,
  rules ← discovery.collect_bundle_members (conf_b ++ sugg_b) >>= load_names,
  rules ← rules.mfilter is_acceptable_rewrite,
  do_rewrite_search cfg $ mk_complete_rewrite_list rules

meta def rewrite_search_using (as : list name) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  check_target,
  exprs ← load_attr_list as >>= load_names,
  hyps ← local_context,
  hyps ← hyps.mfilter (λ h, (do t ← infer_type h, return ¬ t.has_meta_var)),
  rules ← (exprs ++ hyps).mfilter is_acceptable_rewrite,
  do_rewrite_search cfg $ mk_complete_rewrite_list rules

meta def rewrite_search_with (rs : parse rw_rules) (cfg : rewrite_search_config α β γ δ . pick_default_config) : tactic string := do
  check_target,
  rs ← rs.rules.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm)),
  do_rewrite_search cfg rs

  --  exprs ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas

end tactic.interactive
