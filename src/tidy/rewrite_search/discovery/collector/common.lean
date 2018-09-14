import tidy.rewrite_all_wrappers

import ..screening

open tactic

namespace tidy.rewrite_search.discovery

meta def are_promising_rewrites (rws : list (expr × bool)) : list expr → tactic bool
| [] := return false
| (s :: rest) := do
-- TODO alternative (and probably better) condition:
-- tt if the rewrite list contains an expression not seen in the rewrite_search
-- instance, ff otherwise. Maybe too harsh/coarse?
  mllist.empty <$> (all_rewrites_mllist rws s)

meta def is_promising_rewrite (rw : expr × bool) : list expr → tactic bool :=
  are_promising_rewrites [rw]

end tidy.rewrite_search.discovery