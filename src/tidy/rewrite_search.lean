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
  (rewrites : list (ℕ × ℕ))

meta structure node :=
  (lhs rhs               : expr_delta)
  (lhs_pp rhs_pp         : string)
  (lhs_tokens rhs_tokens : list string)
  (distance              : edit_distance_progress lhs_tokens rhs_tokens)

meta def node.to_string (n : node) := n.lhs_pp ++ " = " ++ n.rhs_pp.

-- TODO perhaps also store a hash in node, and compare on that first?
meta def node.equiv (a b : node) : Prop := a.lhs_pp = b.lhs_pp ∧ a.rhs_pp = b.rhs_pp

meta instance : decidable_rel node.equiv := λ a b,
begin
    dunfold node.equiv,
    dunfold id_rhs,
    clear decidable_rel,
    by apply_instance,
end

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
  return ⟨ lhs, rhs, lhs_pp, rhs_pp, lhs_tokens, rhs_tokens, distance ⟩

meta def node.mk'' (lhs rhs : expr) : tactic node :=
do
  lhs_proof ← mk_eq_refl lhs,
  rhs_proof ← mk_eq_refl rhs,
  node.mk' ⟨ lhs, lhs_proof, [] ⟩ ⟨ rhs, rhs_proof, [] ⟩


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
| [] _    := none
| nodes k := match find_first_at nodes k with
                | (some n, r) := some (n, r)
                | (none, r)   := select_next_aux r (k+1)
             end

meta def select_next (nodes: list node) : option (node × (list node)) := select_next_aux nodes 0

meta def new_nodes (rs : list (expr × bool)) (seen_nodes : list node) (n : node) : tactic (list node) := 
do 
  lhs_rewrites ← all_rewrites_list rs n.lhs.current,
  lhs_new_nodes ← lhs_rewrites.mmap $ λ lhs', (do prf ← mk_eq_trans n.lhs.proof lhs'.2.1, node.mk' ⟨ lhs'.1, prf, lhs'.2.2 :: n.lhs.rewrites ⟩ n.rhs),
  rhs_rewrites ← all_rewrites_list rs n.rhs.current,
  rhs_new_nodes ← rhs_rewrites.mmap $ λ rhs', (do prf ← mk_eq_trans n.rhs.proof rhs'.2.1, node.mk' n.lhs ⟨ rhs'.1, prf, rhs'.2.2 :: n.rhs.rewrites ⟩),
  let result := ((lhs_new_nodes ++ rhs_new_nodes).filter $ λ m, ∀ m' ∈ seen_nodes, ¬ (m.equiv m')),
  return result

structure rewrite_search_config :=
  (trace        : bool := ff)
  (trace_result : bool := ff)
  (max_extra_distance : ℕ := 5)

meta def attempt_refl (lhs rhs : expr) : tactic unit :=
lock_tactic_state $
do
  gs ← get_goals,
  m ← to_expr ``(%%lhs = %%rhs) >>= mk_meta_var,
  set_goals [m],
  refl ← mk_const `eq.refl,
  result ← try_core (tactic.apply_core refl {new_goals := new_goals.non_dep_only}),
  set_goals gs,
  guard result.is_some

meta def rewrite_search_core (rs : list (expr × bool)) (cfg : rewrite_search_config := {}) (initial_distance : ℕ) : list node → list node → tactic (option node)
| old_nodes active_nodes := match select_next active_nodes with
            | none := none
            | some (n, r) := 
              do
                if cfg.trace then trace format!"rewrite_search considering node: {n.lhs_pp} = {n.rhs_pp}, distance: {n.distance.to_string}" else skip,
                match n.distance with
                | (exactly _ _ 0) := return (some n)
                | (exactly _ _ k) := do
                                       (attempt_refl n.lhs.current n.rhs.current >> return (some n)) <|>
                                       do
                                        if k > initial_distance + cfg.max_extra_distance then
                                        do
                                          trace format!"max_extra_distance exceeding during rewrite_search",
                                          return none
                                        else
                                        do 
                                          nn ← new_nodes rs (old_nodes ++ active_nodes) n,
                                          rewrite_search_core (n :: old_nodes) (r ++ nn)
                | _ := none --- unreachable code!
                end
            end

meta def rewrite_search (rs : list (expr × bool)) (cfg : rewrite_search_config := {}) (lhs rhs : expr) : tactic (expr_delta × expr_delta) :=
do  first_node ← node.mk'' lhs rhs,
    result ← rewrite_search_core rs cfg (edit_distance_core first_node.distance) [] [first_node],
    match result with 
    | (some n) := return (n.lhs, n.rhs)
    | _        := failed
    end

meta def explain_proof (rs : list string) (p : expr_delta × expr_delta) : string :=
let lhs_steps := p.1.rewrites.reverse.map $ λ q, "perform_nth_rewrite_lhs [" ++ (rs.nth q.1).iget ++ "] " ++ (to_string q.2) in
let rhs_steps := p.2.rewrites.reverse.map $ λ q, "perform_nth_rewrite_rhs [" ++ (rs.nth q.1).iget ++ "] " ++ (to_string q.2) in
string.intercalate ",\n" (lhs_steps ++ rhs_steps)

meta def explain_proof_concisely (rs : list string) (p : expr_delta × expr_delta) : string :=
"erw [" ++ (string.intercalate ", " ((p.1.rewrites.reverse ++ p.2.rewrites.reverse).map $ λ q, (rs.nth q.1).iget)) ++ "]"

meta def check_if_simple_rewrite_succeeds (rs : list (expr × bool)) (p : expr_delta × expr_delta) : tactic unit :=
lock_tactic_state $
focus1 $
do
  t ← target,
  let lhs_rewrites : list (expr × bool) := p.1.rewrites.reverse.map $ λ a, (rs.nth a.1).iget,
  list.mfoldl (λ e : unit, λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}) unit.star lhs_rewrites,
  let rhs_rewrites : list (expr × bool) := p.2.rewrites.reverse.map $ λ a, (rs.nth a.1).iget,
  list.mfoldl (λ e : unit, λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}) unit.star rhs_rewrites,
  reflexivity.

meta def rewrite_search_target (rs : list (expr × bool)) (cfg : rewrite_search_config := {}) : tactic string :=
do t ← target,
   match t with
   | `(%%lhs = %%rhs) := do
                           (r1, r2) ← rewrite_search rs cfg lhs rhs,
                           prf2 ← mk_eq_symm r2.proof,
                           prf ← mk_eq_trans r1.proof prf2,
                           if cfg.trace then
                             do trace "rewrite_search found proof:", trace prf
                           else skip,
                           rs_strings ← rs.mmap (λ p, (do pp ← pretty_print p.1, return (if p.2 then ("←" ++ pp) else pp))),
                           explanation ← (do 
                             check_if_simple_rewrite_succeeds rs (r1, r2),
                              return (explain_proof_concisely rs_strings (r1, r2))) <|> return (explain_proof rs_strings (r1, r2)),
                           if cfg.trace_result then trace explanation
                           else skip,
                           exact prf,
                           return explanation
   | _ := fail "target is not an equation"
   end

end tidy.rewrite_search

namespace tactic.interactive

open tidy.rewrite_search
open interactive interactive.types expr tactic

meta def rewrite_search (rs: parse rw_rules) (cfg : rewrite_search_config := {}) : tactic string :=
do rs ← rs.rules.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm)),
   rewrite_search_target rs cfg

meta def rewrite_search_using (a : name) (cfg : rewrite_search_config := {}) : tactic string :=
do names ← attribute.get_instances a,
   exprs ← names.mmap $ mk_const,
   hyps ← local_context,
   let exprs := exprs ++ hyps,
   let pairs := exprs.map (λ e, (e, ff)) ++ exprs.map (λ e, (e, tt)),
   rewrite_search_target pairs cfg

end tactic.interactive

meta def search_attribute : user_attribute := {
  name := `search,
  descr := ""
}

run_cmd attribute.register `search_attribute

-- PROJECT cache all_rewrites_list?
