import tidy.rewrite_all_wrappers

import .primitives

namespace tidy.rewrite_search

inductive how
| rewrite (rule_index : ℕ) (side : side) (location : ℕ)
| defeq

meta structure rewrite :=
(e prf : expr)
(how : how)

-- TODO once partial rewriting is implemented, use this to hold the
-- partial rewrite state.
meta structure rewrite_progress :=
(dummy : unit)

-- TODO apply simp and add the resulting rewrite to the list generated below, if simp did anything

-- @Scott
-- TODO once partial rewriting is implemented, this will inspect the passed rewrite_progress data
-- and return a list of one (or more, if convenient) `rewrite`s for addition to the rewrite table.
-- We return the updated mutable progress state, along with the list we generated. If there are no
-- more rewrtes, return an empty list---the handler functions will understand.
-- Remark: the first time we ever get called, we get passed prog = none.
meta def discover_more_rewrites (rs : list (expr × bool)) (exp : expr) (cfg : rewrite_all_cfg) (s : side) : option rewrite_progress → tactic (option rewrite_progress × list rewrite)
| (some prog) := return (some prog, [])
| none := do
  all_rws ← all_rewrites_list rs exp cfg,
  let all_rws : list rewrite := all_rws.map (λ t, ⟨t.1, t.2.1, how.rewrite t.2.2.1 s t.2.2.2⟩),
  return (some ⟨()⟩, all_rws)

end tidy.rewrite_search