import tidy.rewrite_search.core.shared

import .shared
import .bundle

universe u

open tidy.rewrite_search

namespace tidy.rewrite_search.discovery

meta def discovery_trace {α : Type u} [has_to_tactic_format α] (a : α) (nl : bool := tt) : tactic unit := do
  str ← tactic.pp a,
  let nlc := if nl then "\n" else "",
  cur ← tactic.decl_name,
  tactic.trace format!"(discovery@{cur}): {str}{nlc}"

meta def collector := config → progress → list expr → tactic (progress × list (expr × bool))

end tidy.rewrite_search.discovery