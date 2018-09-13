import tidy.lib.env
import tidy.rewrite_search.core.shared

import .types
import .screening
import .bundle
import .suggest
import .collector

open tactic
open tidy.rewrite_search

universe u

namespace tidy.rewrite_search.discovery

-- TODO trace only when we have success.
-- TODO add configurable "persistence"

meta def default_collectors : list collector := [try_bundles, try_everything]

/-- Bundle names are names like ```logic``. -/
meta def collect (use_suggest_annotations : bool) (p : persistence) (suggested_bundle_names : list name) (extra_names : list name) : tactic (progress × list (expr × bool)) := do
  n_bs ← suggested_bundle_names.mmap get_bundle,
  i_bs ← if use_suggest_annotations then get_suggested_bundle_idents >>= list.mmap lookup_bundle else pure [],
  let bs := n_bs ++ i_bs,
  exprs ← collect_bundle_members bs >>= load_names,
  extra_exprs ← load_names extra_names,
  extra_exprs.mmap assert_acceptable_lemma,
  return (⟨p, bs⟩, rewrite_list_from_lemmas $ exprs ++ extra_exprs)

-- Currently, we guarentee that each rewrite we return gives some expression the environment
-- hasn't seen before.
meta def collect_more_using : list collector → config → progress → list expr → tactic (progress × list (expr × bool))
| [] conf p _ := do
  if conf.trace_discovery ∧ ¬(p.persistence = persistence.speedy) then
    discovery_trace "Giving up." ff
  else skip,
  return (p, [])
| (fn :: rest) conf p sample := do
  (p, rws) ← fn conf p sample,
  if rws.length = 0 then
    collect_more_using rest conf p sample
  else
    return (p, rws)

meta def collect_more (conf : config) (prog : progress) (sample : list expr) : tactic (progress × list (expr × bool)) := do
  if conf.trace_discovery ∧ ¬(prog.persistence = discovery.persistence.speedy) then
    tactic.trace "rewrite_search is getting desperate...\n"
  else skip,
  collect_more_using default_collectors conf prog sample

end tidy.rewrite_search.discovery