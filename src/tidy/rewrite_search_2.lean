-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Barter, Louis Carlin, Scott Morrison, Sam Quinn

import data.list
import data.option
import .edit_distance
import .pretty_print
import .rewrite_all

namespace tidy.rewrite_search

open edit_distance_progress
open tactic

meta structure expr_delta :=
  (current : expr)
  (proof   : expr)

meta structure node :=
  (lhs rhs               : expr_delta)
  (lhs_tokens rhs_tokens : list string)
  (distance              : edit_distance_progress lhs_tokens rhs_tokens)

meta def node.equiv (a b : node) : Prop := a.lhs_tokens = b.lhs_tokens ∧ a.rhs_tokens = b.lhs_tokens
meta instance : decidable_rel node.equiv := sorry

meta def node.distance_bound (n : node) :=
match n.distance with
| exactly _ _ k    := k
| at_least _ _ k _ := k
end

meta def node.mk' (lhs rhs : expr_delta) : tactic node :=
do
  lhs_pp ← pretty_print lhs.current,
  rhs_pp ← pretty_print rhs.current,
  let lhs_tokens := lhs_pp.split_on ' ',
  let rhs_tokens := rhs_pp.split_on ' ',
  let distance := at_least lhs_tokens rhs_tokens 0 (empty_partial_edit_distance_data lhs_tokens rhs_tokens),
  return ⟨ lhs, rhs, lhs_tokens, rhs_tokens, distance ⟩

meta def node.mk'' (lhs rhs : expr) : tactic node :=
do
  lhs_proof ← mk_eq_refl lhs,
  rhs_proof ← mk_eq_refl rhs,
  node.mk' ⟨ lhs, lhs_proof ⟩ ⟨ rhs, rhs_proof ⟩


open list

meta def find_first_at : list node → ℕ → (option node) × list node
| nil k      := (none, nil)
| (h :: t) k := if h.distance_bound = k then
                  match h.distance with
                  | exactly _ _ _ := (some h, t)
                  | at_least _ _ _ d := 
                      match update_edit_distance h.distance with
                      | exactly _ _ k := (some { h with distance := exactly _ _ k }, t)
                      | ed            := 
                          match find_first_at t k with
                          | (o, l) := (o, { h with distance := ed } :: l)
                          end
                      end
                  end
                else
                  match find_first_at t k with
                  | (o, l) := (o, h :: l)
                  end


meta def select_next_aux : list node → ℕ → option (node × (list node))
| nodes k := match find_first_at nodes k with
                | (some n, r) := some (n, r)
                | (none, r)   := select_next_aux r (k+1)
             end

meta def select_next (nodes: list node) : option (node × (list node)) := select_next_aux nodes 0

meta def new_nodes (rs : list (expr × bool)) (old_nodes : list node) (n : node) : tactic (list node) := 
do 
  lhs_rewrites ← all_rewrites_list rs n.lhs.current,
  lhs_new_nodes ← lhs_rewrites.mmap $ λ lhs', (do prf ← mk_eq_trans n.lhs.proof lhs'.2, node.mk' ⟨ lhs'.1, prf ⟩ n.rhs),
  rhs_rewrites ← all_rewrites_list rs n.rhs.current,
  rhs_new_nodes ← rhs_rewrites.mmap $ λ rhs', (do prf ← mk_eq_trans n.rhs.proof rhs'.2, node.mk' n.lhs ⟨ rhs'.1, prf ⟩),
  return ((lhs_new_nodes ++ rhs_new_nodes).filter $ λ m, ∀ m' ∈ old_nodes, ¬ (m.equiv m'))

meta def rewrite_search_core (rs : list (expr × bool)) : list node → list node → tactic (option node)
| old_nodes active_nodes := match select_next active_nodes with
            | none := none
            | some (n, r) := match n.distance with
                | (exactly _ _ 0) := return (some n)
                | (exactly _ _ k) := do
                                       nn ← new_nodes rs old_nodes n,
                                       rewrite_search_core (n :: old_nodes) (r ++ nn)
                | _ := none --- unreachable code!
                end
            end

meta def rewrite_search' (rs : list (expr × bool)) (lhs rhs : expr) : tactic (expr_delta × expr_delta) :=
do  first_node ← node.mk'' lhs rhs,
    result ← rewrite_search_core rs [] [first_node],
    match result with 
    | (some n) := return (n.lhs, n.rhs)
    | _        := failed
    end

meta def rewrite_search (rs : list (expr × bool)) : tactic unit :=
do t ← target,
   match t with
   | `(%%lhs = %%rhs) := do
                           (r1, r2) ← rewrite_search' rs lhs rhs,
                           prf2 ← mk_eq_symm r2.proof,
                           prf ← mk_eq_trans r1.proof prf2,
                           exact prf
   | _ := fail "target is not an equation"
   end

end tidy.rewrite_search

namespace tactic.interactive

open interactive interactive.types expr

meta def rewrite_search (rs: parse rw_rules) : tactic unit :=
do rs ← rs.rules.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm)),
   tidy.rewrite_search.rewrite_search rs

end tactic.interactive

-- TODO test!
-- TODO make sure all_rewrites_list is cached?
