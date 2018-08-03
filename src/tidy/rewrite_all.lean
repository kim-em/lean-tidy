-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import data.list
import .pretty_print

open tactic
open interactive
open interactive.types
open expr
open lean
open lean.parser

meta def lock_tactic_state {α} (t : tactic α) : tactic α
| s := match t s with
       | result.success a s' := result.success a s
       | result.exception msg pos s' := result.exception msg pos s
       end

meta def rewrite_without_new_mvars (r : expr) (e : expr) (cfg : rewrite_cfg := {}) : tactic (expr × expr) :=
lock_tactic_state $ -- This makes sure that we forget everything in between rewrites; otherwise we don't correctly find everything!
do n_before ← num_goals,
   (new_t, prf, metas) ← rewrite_core r e cfg,
   try_apply_opt_auto_param cfg.to_apply_cfg metas,
   n_after ← num_goals,
   guard (n_before = n_after),
   prf ← instantiate_mvars prf, -- This is necessary because of the locked tactic state.
   return (new_t, prf)

open tactic.interactive

meta inductive expr_lens
| app_fun : expr_lens → expr → expr_lens
| app_arg : expr_lens → expr → expr_lens
| entire  : expr_lens

open expr_lens

meta def expr_lens.replace : expr_lens → expr → expr
| (app_fun l f) x := expr_lens.replace l (expr.app f x)
| (app_arg l x) f := expr_lens.replace l (expr.app f x)
| entire        e := e 

meta def local_def_value (e : expr) : tactic expr := do
do (v,_) ← solve_aux `(true) (do
         lc ← local_context,
         let e := lc.reverse.head,
         (expr.elet n t v _) ← (revert e >> target)
           | fail format!"{e} is not a local definition",
         return v),
   return v

meta def mk_congr_arg_using_dsimp (G W : expr) (F : name) : tactic expr := 
-- lock_tactic_state $
do
  s ← simp_lemmas.mk_default,
  t ← infer_type G,
  t' ← s.dsimplify [F] t {fail_if_unchanged := ff},
  tactic.definev `g t' G,
  ca ← to_expr ```(congr_arg (g : %%t') %%W),
  ca_t ← infer_type ca,
  he ← tactic.definev `h ca_t ca,
  `[dsimp [g] at h],
  local_def_value he

meta def expr_lens.congr : expr_lens → expr → tactic expr
| (app_fun l f) x_eq := do 
                                         tactic.trace "dsimp'ing f",
                                         s ← simp_lemmas.mk_default,
                                         f' ← s.dsimplify [`has_coe_to_fun.F] f {fail_if_unchanged := ff},
                                         ft ← infer_type f',
                                         tactic.trace ft,
                                         ft' ← s.dsimplify [`has_coe_to_fun.F] ft {fail_if_unchanged := ff},
                                         tactic.trace ft',
                                         f'' ← to_expr ``(%%f' : %%ft'),
                                         x_eq_t ← infer_type x_eq,
                          fx_eq ← try_core (
                                      -- to_expr ```(congr_arg (%%f' : %%ft') %%x_eq)
                                      mk_congr_arg_using_dsimp f x_eq `has_coe_to_fun.F
                                    ),
                           match fx_eq with
                           | (some fx_eq) := expr_lens.congr l fx_eq
                           | none         := do 
                                                pp_f ← pretty_print f'' tt,
                                                pp_ft ← pretty_print ft' tt,
                                                pp_x_eq ← pretty_print x_eq tt,
                                                pp_x_eq_t ← pretty_print x_eq_t tt,
                                                tactic.trace format!"expr_lens.congr failed on \n{pp_f} : {pp_ft}\n{pp_x_eq} : {pp_x_eq_t}" >> failed
                           end
| (app_arg l x) f_eq := do fx_eq ← mk_congr_fun f_eq x,
                                    expr_lens.congr l fx_eq
| entire                  e_eq := pure e_eq

meta def rewrite_fold_aux {α} (F : expr_lens → expr → α → tactic α) : expr_lens → expr → α → tactic α 
| l e a := (do a' ← F l e a,
              match e with
              | (expr.app f x) := do a_f ← rewrite_fold_aux (expr_lens.app_arg l x) f a',
                                            rewrite_fold_aux (expr_lens.app_fun l f) x a_f
              | _ := pure a'
              end) <|> pure a
. 

meta def rewrite_fold {α} (F : expr_lens → expr → α → tactic α) (e : expr) (a : α) : tactic α := rewrite_fold_aux F expr_lens.entire e a

-- This is a bit of a hack: we manually inspect the proof that `rewrite_core` produced, and deduce from that whether or not the entire expression was rewritten.
meta def rewrite_is_of_entire' : expr → bool
| `(@eq.rec _ %%term %%C %%p _ _) := match p with
                                     | `(@eq.refl _ %%term') := term = term'
                                     | _ := ff
                                     end
| _ := ff
meta def rewrite_is_of_entire : expr → bool
| `(@eq.rec _ %%term %%C %%p _ _) := match C with
                                     | `(λ p, _ = p) := tt
                                     | _ := ff
                                     end
| _ := ff

meta def rewrite_F (r : expr × bool) (l : expr_lens) (e : expr) (state : list (expr × expr)) : tactic (list (expr × expr)) := 
do 
  -- pp_e ← pretty_print e,
  -- pp_r ← pretty_print r.1,
  -- tactic.trace ("attempting rewrite on " ++ pp_e ++ " using " ++ (if r.2 then "←" else "") ++ pp_r),
  (v, pr) ← rewrite_without_new_mvars r.1 e {symm := r.2, md := semireducible},
  -- pp_v ← pretty_print v,
  -- tactic.trace pp_v,
  -- pp_pr ← pretty_print pr tt,
  -- tactic.trace pp_pr,
  -- Now we determine whether the rewrite transforms the entire expression or not:
  if rewrite_is_of_entire pr then
  do
    -- tactic.trace ("rewrite succeeded, complete!"),
    let w' := l.replace v,
    qr' ←  try_core (l.congr pr),
    match qr' with
    | none       := tactic.trace "Uh oh, expr_lens.congr failed!" >> failed
    | (some qr') := pure ((w', qr') :: state)
    end
  else 
  do 
    -- tactic.trace ("rewrite succeeded, tunneling!"),
    pure state

def remove_adjacent_duplicates {α β} (f : α → β) [decidable_eq β] : list α → list α
| (x :: y :: t) := if f x = f y then
                     remove_adjacent_duplicates (y :: t)
                   else
                     x :: (remove_adjacent_duplicates (y :: t))
| [x] := [x]
| [] := []


meta def remove_duplicates {α β} (f : α → β) [decidable_eq β] : list α → list α
| (x :: t) := x :: (remove_duplicates (t.filter $ λ a, f a ≠ f x))
| [] := []


meta def all_rewrites (r : expr × bool) (e : expr) : tactic (list (expr × expr)) :=
do 
   results ← rewrite_fold (rewrite_F r) e [],
  --  tactic.trace results,
   return (remove_adjacent_duplicates (λ p, p.1) results)

-- return a list of (e', prf, n, k) where 
--   e' is a new expression, 
--   prf : e = e', 
--   n is the index of the rule r used from rs, and 
--   k is the index of (e', prf) in all_rewrites r e.
meta def all_rewrites_list (rs : list (expr × bool)) (e : expr) : tactic (list (expr × expr × ℕ × ℕ)) :=
do
  results ← rs.mmap $ λ r, all_rewrites r e,
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

meta def perform_nth_rewrite_lhs (q : parse rw_rules) (n : ℕ) : tactic unit := 
do `(%%lhs = %%rhs) ← target,
   (new_t, prf) ← perform_nth_rewrite' q n lhs,
   replace_target_lhs new_t prf,
   tactic.try tactic.reflexivity

meta def perform_nth_rewrite_rhs (q : parse rw_rules) (n : ℕ) : tactic unit := 
do `(%%lhs = %%rhs) ← target,
   (new_t, prf) ← perform_nth_rewrite' q n rhs,
   replace_target_rhs new_t prf,
   tactic.try tactic.reflexivity


meta def perform_nth_rewrite_using (a : name) (n : ℕ) : tactic unit := 
do e ← target,
   rewrites ← all_rewrites_using a e,
   (new_t, prf) ← rewrites.nth n,
   replace_target new_t prf

end tactic.interactive