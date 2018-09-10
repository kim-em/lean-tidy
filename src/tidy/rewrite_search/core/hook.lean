import data.list
import tidy.mllist
import tidy.rewrite_all_wrappers

import .primitives

namespace tidy.rewrite_search

inductive how
| rewrite (rule_index : ℕ) (side : side) (location : ℕ)
| defeq
| simp  -- TODO handle "explaining" me

meta structure rewrite :=
(e   : expr)
(prf : tactic expr) -- we defer constructing the proofs until they are needed
(how : how)

meta structure rewrite_progress :=
(list : mllist tactic rewrite)

open tactic

-- TODO Am I even good? Do I work? Do I slow us down too much?
meta def simp_expr (t : expr) (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic (expr × expr) := do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  simplify s to_unfold t cfg `eq discharger

meta def dsimp_expr (t : expr) (no_defaults := ff) (attr_names : list name := []) (hs : list simp_arg_type := []) (cfg : dsimp_config := {}) (discharger : tactic unit := failed) : tactic expr := do
  (s, to_unfold) ← mk_simp_set no_defaults attr_names hs,
  s.dsimplify to_unfold t cfg

-- @Scott
-- TODO once partial rewriting is implemented, this will inspect the passed rewrite_progress data
-- and return a list of one (or more, if convenient) `rewrite`s for addition to the rewrite table.
-- We return the updated mutable progress state, along with the list we generated. If there are no
-- more rewrtes, return an empty list---the handler functions will understand.
-- Remark: the first time we ever get called, we get passed prog = none.
meta def discover_more_rewrites_old (rs : list (expr × bool)) (exp : expr) (cfg : rewrite_all_cfg) (s : side) : option rewrite_progress → tactic (option rewrite_progress × list rewrite)
| (some prog) := return (some prog, [])
| none := do
  all_rws ← all_rewrites_list rs exp cfg,
  let all_rws : list rewrite := all_rws.map (λ t, ⟨t.1, t.2.1, how.rewrite t.2.2.1 s t.2.2.2⟩),
  all_rws ← (do (simp_exp, simp_prf) ← simp_expr exp,
                pure $ all_rws.concat ⟨simp_exp, pure simp_prf, how.simp⟩)
            <|> pure all_rws,
  return (some ⟨mllist.nil⟩, all_rws)

meta def discover_more_rewrites (rs : list (expr × bool)) (exp : expr) (cfg : rewrite_all_cfg) (s : side) : option rewrite_progress → tactic (option rewrite_progress × list rewrite)
| (some ⟨ mllist.nil ⟩) := fail "no more rewrites available"
| (some ⟨ mllist.cons a L ⟩) := do r ← L, return (some ⟨ r ⟩, [a])
| none := do
  all_rws ← all_rewrites_mllist rs exp cfg,
  all_rws ← all_rws.map (λ t, { rewrite . e := t.1, prf := t.2.1, how := how.rewrite t.2.2.1 s t.2.2.2 }),
  -- TODO hook up `simp` again.
  -- all_rws ← (do (simp_exp, simp_prf) ← simp_expr exp,
  --               pure $ all_rws.concat ⟨simp_exp, pure simp_prf, how.simp⟩)
  --           <|> pure all_rws,
  discover_more_rewrites (some ⟨ all_rws ⟩)


end tidy.rewrite_search
