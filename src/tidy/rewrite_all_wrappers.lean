import .rewrite_all

open tactic
open lean.parser
open interactive

-- TODO is this necessary?!
meta def remove_duplicates {α β} (f : α → β) [decidable_eq β] : list α → list α
| (x :: t) := x :: (remove_duplicates (t.filter $ λ a, f a ≠ f x))
| [] := []

-- return a list of (e', prf, n, k) where
--   e' is a new expression,
--   prf : e = e',
--   n is the index of the rule r used from rs, and
--   k is the index of (e', prf) in all_rewrites r e.
meta def all_rewrites_list (rs : list (expr × bool)) (e : expr) (cfg : rewrite_all_cfg := {md := semireducible}) : tactic (list (expr × expr × ℕ × ℕ)) :=
do
  results ← rs.mmap $ λ r, all_rewrites r e cfg,
  let results' := results.enum.map (λ p, p.2.enum.map (λ q, (q.2.1, q.2.2, p.1, q.1))),
return (remove_duplicates (λ t, t.1) results'.join)

meta def perform_nth_rewrite (r : expr × bool) (n : ℕ) : tactic unit :=
do e ← target,
   rewrites ← all_rewrites r e,
   (new_t, prf) ← rewrites.nth n,
   replace_target new_t prf

meta def all_rewrites_using (a : name) (e : expr) : tactic (list (expr × expr)) :=
do names ← attribute.get_instances a,
   rules ← names.mmap $ mk_const,
   let pairs := rules.map (λ e, (e, ff)) ++ rules.map (λ e, (e, tt)),
   results ← pairs.mmap $ λ r, all_rewrites r e,
   pure results.join

namespace tactic.interactive

private meta def perform_nth_rewrite' (q : parse rw_rules) (n : ℕ) (e : expr) : tactic (expr × expr) :=
do rewrites ← q.rules.mmap $ λ p : rw_rule, to_expr p.rule tt ff >>= λ r, all_rewrites (r, p.symm) e,
   let rewrites := rewrites.join,
   rewrites.nth n

meta def perform_nth_rewrite (q : parse rw_rules) (n : ℕ) : tactic unit :=
do e ← target,
   (new_t, prf) ← perform_nth_rewrite' q n e,
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
   (new_t, prf) ← perform_nth_rewrite' q n lhs,
   replace_target_lhs new_t prf,
   tactic.try tactic.reflexivity

meta def nth_rewrite_rhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%lhs = %%rhs) ← target,
   (new_t, prf) ← perform_nth_rewrite' q n rhs,
   replace_target_rhs new_t prf,
   tactic.try tactic.reflexivity

end tactic.interactive
