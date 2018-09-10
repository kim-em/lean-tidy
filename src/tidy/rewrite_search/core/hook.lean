import tidy.lib.tactic
import tidy.rewrite_all_wrappers

import .primitives

namespace tidy.rewrite_search

meta def rewrite_progress := mllist tactic rewrite

meta def progress_init (rs : list (expr × bool)) (exp : expr) (cfg : rewrite_all_cfg) (s : side) : tactic rewrite_progress := do
  l ← all_rewrites_list rs exp cfg,
  l.map (λ t, ⟨t.1, t.2.1, how.rewrite t.2.2.1 s t.2.2.2⟩)

meta def progress_next : rewrite_progress → tactic (rewrite_progress × option rewrite)
| mllist.nil        := return (mllist.nil, none)
| (mllist.cons a l) := do r ← l, return (r, some a)

meta def try_simp_rewrite (exp : expr) : tactic (option rewrite) := do
  (do (simp_exp, simp_prf) ← tactic.simp_expr exp,
      return $ some ⟨simp_exp, pure simp_prf, how.simp⟩)
  <|> return none

-- FIXME I don't know how to extract a proof of equality from `simp_lemmas.dsimplify`
-- meta def try_dsimp_rewrite (exp : expr) : tactic (option rewrite) := do
--   (do dsimp_exp ← tactic.dsimp_expr exp,
--       return $ some ⟨dsimp_exp, ???, how.defeq⟩)
--   <|> return none

meta def discover_more_rewrites (rs : list (expr × bool)) (exp : expr) (cfg : rewrite_all_cfg) (s : side) (prog : option rewrite_progress) : tactic (option rewrite_progress × list rewrite) := do
  (prog, head) ← match prog with
         | some prog := pure (prog, [])
         | none := do
          prog ← progress_init rs exp cfg s,
          sl ← try_simp_rewrite exp,
          pure (prog, sl.to_list)
         end,
  (prog, rw) ← progress_next prog,
  return (some prog, head.append rw.to_list)

end tidy.rewrite_search
