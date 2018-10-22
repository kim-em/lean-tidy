import .rewrite_all_congr

open tactic
open lean.parser
open interactive

-- TODO We currently don't use `list.erase_duplicates`. Is it necessary?!

-- return a list of (e', prf, n, k) where
--   e' is a new expression,
--   prf : e = e',
--   n is the index of the rule r used from rs, and
--   k is the index of (e', prf) in all_rewrites r e.
meta def all_rewrites_mllist (rs : list (expr × bool)) (e : expr) (cfg : rewrite_all_cfg := {md := semireducible}) : tactic (mllist tactic (tracked_rewrite × ℕ × ℕ)) := do
  l ← rs.mmap $ λ r, all_rewrites_lazy r e cfg,
  l ← l.enum.mmap (λ p, do
    pe ← p.2.enum,
    pe.map (λ q, (q.2, p.1, q.1))
  ),
  (mllist.of_list l).join

meta def all_rewrites_list (rs : list (expr × bool)) (e : expr) (cfg : rewrite_all_cfg := {md := semireducible}) : tactic (list (tracked_rewrite × ℕ × ℕ)) :=
  all_rewrites_mllist rs e cfg >>= mllist.force

meta def perform_nth_rewrite (r : expr × bool) (n : ℕ) : tactic unit :=
do e ← target,
   rewrites ← all_rewrites r e,
   lrw ← rewrites.nth n,
   lrw.proof >>= replace_target lrw.exp

meta def all_rewrites_using (a : name) (e : expr) : tactic (list tracked_rewrite) :=
do names ← attribute.get_instances a,
   rules ← names.mmap $ mk_const,
   let pairs := rules.map (λ e, (e, ff)) ++ rules.map (λ e, (e, tt)),
   results ← pairs.mmap $ λ r, all_rewrites r e,
   pure results.join

namespace tactic.interactive

private meta def perform_nth_rewrite' (n : parse small_nat) (q : parse rw_rules) (e : expr) : tactic (expr × expr) :=
do rewrites ← q.rules.mmap $ λ p : rw_rule, to_expr p.rule tt ff >>= λ r, all_rewrites (r, p.symm) e,
   let rewrites := rewrites.join,
   guard (n < rewrites.length) <|> fail format!"failed: not enough rewrites found",
   lrw ← rewrites.nth n,
   pf ← lrw.proof,
   return (lrw.exp, pf)

meta def perform_nth_rewrite (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do e ← target,
   (new_t, prf) ← perform_nth_rewrite' n q e,
  --  trace new_t,
  --  trace prf,
   replace_target new_t prf,
   tactic.try tactic.reflexivity

meta def replace_target_lhs (new_lhs prf: expr) : tactic unit :=
do `(%%lhs = %%rhs) ← target,
   new_target ← to_expr ``(%%new_lhs = %%rhs) tt ff,
   prf' ← to_expr ``(congr_arg (λ L, L = %%rhs) %%prf) tt ff,
   replace_target new_target prf'

meta def replace_target_rhs (new_rhs prf: expr) : tactic unit :=
do `(%%lhs = %%rhs) ← target,
   new_target ← to_expr ``(%%lhs = %%new_rhs) tt ff,
   prf' ← to_expr ``(congr_arg (λ R, %%lhs = R) %%prf) tt ff,
   replace_target new_target prf'

meta def nth_rewrite_lhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%lhs = %%rhs) ← target,
   (new_t, prf) ← perform_nth_rewrite' n q lhs,
   replace_target_lhs new_t prf,
   tactic.try tactic.reflexivity

meta def nth_rewrite_rhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%lhs = %%rhs) ← target,
   (new_t, prf) ← perform_nth_rewrite' n q rhs,
   replace_target_rhs new_t prf,
   tactic.try tactic.reflexivity

end tactic.interactive
