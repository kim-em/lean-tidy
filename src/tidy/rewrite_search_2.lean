-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Barter, Louis Carlin, Scott Morrison, Sam Quinn

import data.list
import data.option
import .edit_distance
import .pretty_print
import .rewrite_all

open edit_distance_progress

meta structure node :=
  (lhs : expr)
  (rhs : expr)
  (lhs_pp : string)
  (rhs_pp : string)
  (lhs_tokens : list string)
  (rhs_tokens : list string)
  (distance : edit_distance_progress lhs_tokens rhs_tokens)

meta def node.distance_bound (n : node) :=
match n.distance with
| exactly _ _ k := k
| at_least _ _ k _ := k
end

meta def node.mk' (lhs rhs : expr) : tactic node :=
do
  lhs_pp ← pretty_print lhs,
  rhs_pp ← pretty_print rhs,
  let lhs_tokens := lhs_pp.split_on ' ',
  let rhs_tokens := rhs_pp.split_on ' ',
  let distance := at_least lhs_tokens rhs_tokens 0 (empty_partial_edit_distance_data lhs_tokens rhs_tokens),
  return ⟨ lhs, rhs, lhs_pp, rhs_pp, lhs_tokens, rhs_tokens, distance ⟩

open list

meta def find_first_at : list node → ℕ → (option node) × list node
| nil k      := (none, nil)
| (h :: t) k := if h.distance_bound = k then
                  match h.distance with
                  | exactly _ _ _ := (some h, t)
                  | at_least _ _ _ d := match update_edit_distance h.distance with
                                        | exactly _ _ k := (some { h with distance := exactly _ _ k }, t)
                                        | ed            := match find_first_at t k with
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

meta def new_nodes (rs : list (expr × bool)) (n : node) : tactic (list node) := 
do 
  lhs_rewrites ← all_rewrites_list rs n.lhs,
  lhs_new_nodes ← lhs_rewrites.mmap $ λ lhs', node.mk' lhs'.1 n.rhs,
  rhs_rewrites ← all_rewrites_list rs n.rhs,
  rhs_new_nodes ← rhs_rewrites.mmap $ λ rhs', node.mk' n.lhs rhs'.1,
  return (lhs_new_nodes ++ rhs_new_nodes)

meta def rewrite_search_core (rs : list (expr × bool)) : list node → tactic (option node)
| nodes := match select_next nodes with
            | none := none
            | some (n, r) := match n.distance with
                | (exactly _ _ 0) := return (some n)
                | (exactly _ _ k) := do
                                       nn ← new_nodes rs n,
                                       rewrite_search_core (r ++ nn)
                | _ := none --- unreachable code!
                end
            end

meta def rewrite_search (rs : list (expr × bool)) (lhs rhs : expr) : tactic (option node) :=
do  first_node ← node.mk' lhs rhs,
    rewrite_search_core rs [first_node]


-- TODO make sure all_rewrites_list is cached?
-- TODO we need to keep track of the proofs!
-- TODO we need a wrapper around rewrite_search so it's actually usable.