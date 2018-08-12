-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Daniel Barter, Louis Carlin, Scott Morrison, Sam Quinn, Simon Hudon

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

/- `find_first_node_at_distance nodes k` returns the first node in `nodes` that is at distance exactly `k`, if there is one,
   along with a list of all the other nodes, possibly with their distance bounds improved. -/
meta def find_first_node_at_distance : list node → ℕ → (option node) × list node
| nil k      := (none, nil)
| (h :: t) k := if h.distance_bound = k then
                  match h.distance with
                  | exactly _ _ _ := (some h, t)
                  | at_least _ _ _ d := 
                      let ed := update_edit_distance h.distance in
                      if ed = exactly _ _ k then
                        (some { h with distance := exactly _ _ k }, t)
                      else
                        match find_first_node_at_distance t k with
                          | (o, l) := (o, { h with distance := ed } :: l)
                          end                      
                  end
                else
                  match find_first_node_at_distance t k with
                  | (o, l) := (o, h :: l)
                  end

meta def select_next_aux : list node → ℕ → option (node × (list node))
| [] _    := none
| nodes k := match find_first_node_at_distance nodes k with
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
  (trace         : bool := ff)
  (trace_goal    : bool := ff)
  (trace_result  : bool := ff)
  (trace_rules   : bool := ff)
  (trace_summary : bool := ff)
  (max_steps          : option ℕ := none)
  (max_extra_distance : option ℕ := some 50)

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

meta def rewrite_search_core (rs : list (expr × bool)) (cfg : rewrite_search_config := {}) (initial_distance : ℕ) : list node → list node → tactic (ℕ × ℕ × option node)
| old_nodes active_nodes := 
   if cfg.max_steps.is_some ∧ old_nodes.length ≥ cfg.max_steps.get_or_else 0 then
   do
     trace "max_steps exceeded during rewrite_search",
     active_nodes.mmap' $ λ m, trace (m.lhs_pp ++ " = " ++ m.rhs_pp ++ ", distance ≥ " ++ (to_string m.distance_bound)),
     return (old_nodes.length, active_nodes.length, none)
   else
      match select_next active_nodes with
      | none := return (old_nodes.length, active_nodes.length, none)
      | some (n, r) := 
        do
          if cfg.trace then trace format!"rewrite_search considering node: {n.lhs_pp} = {n.rhs_pp}, distance: {n.distance.to_string}" else skip,
          match n.distance with
          | (exactly _ _ 0) := return (old_nodes.length, active_nodes.length, some n)
          | (exactly _ _ k) := 
            do
              (attempt_refl n.lhs.current n.rhs.current >> return (old_nodes.length, active_nodes.length, some n)) <|>
              do
                if cfg.max_extra_distance.is_some ∧ k > initial_distance + cfg.max_extra_distance.get_or_else 0 then
                do
                  trace "max_extra_distance exceeded during rewrite_search",
                  return (old_nodes.length, active_nodes.length, none)
                else
                do 
                  nn ← new_nodes rs (old_nodes ++ active_nodes) n,
                  rewrite_search_core (n :: old_nodes) (r ++ nn)
          | _ := fail "unreachable code!"
          end
      end

meta def rewrite_search (rs : list (expr × bool)) (cfg : rewrite_search_config := {}) (lhs rhs : expr) : tactic (ℕ × ℕ × expr_delta × expr_delta) :=
do  first_node ← node.mk'' lhs rhs,
    result ← rewrite_search_core rs cfg (edit_distance_core first_node.distance) [] [first_node],
    match result with 
    | (steps, remaining, (some n)) := return (steps, remaining, n.lhs, n.rhs)
    | (_, 0, none)                 := fail "rewrite_search exhausted the rewrite graph"
    | (_, _, none)                 := fail "rewrite_search stopped because it exceeded a limit"
    end

meta def explain_proof (rs : list string) (p : expr_delta × expr_delta) : string :=
let lhs_steps := p.1.rewrites.reverse.map $ λ q, "perform_nth_rewrite_lhs [" ++ (rs.nth q.1).iget ++ "] " ++ (to_string q.2) in
let rhs_steps := p.2.rewrites.reverse.map $ λ q, "perform_nth_rewrite_rhs [" ++ (rs.nth q.1).iget ++ "] " ++ (to_string q.2) in
string.intercalate ",\n" (lhs_steps ++ rhs_steps)

meta def explain_proof_concisely (rs : list string) (p : expr_delta × expr_delta) (needs_refl : bool) : string :=
"erw [" ++ (string.intercalate ", " ((p.1.rewrites.reverse ++ p.2.rewrites.reverse).map $ λ q, (rs.nth q.1).iget)) ++ "]" ++ (if needs_refl then ", refl" else "")

-- fails if we can't just use rewrite
-- otherwise, returns 'tt' if we need a `refl` at the end
meta def check_if_simple_rewrite_succeeds (rs : list (expr × bool)) (p : expr_delta × expr_delta) : tactic bool :=
lock_tactic_state $
focus1 $
do
  t ← target,
  let lhs_rewrites : list (expr × bool) := p.1.rewrites.reverse.map $ λ a, (rs.nth a.1).iget,
  list.mfoldl (λ e : unit, λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}) unit.star lhs_rewrites,
  let rhs_rewrites : list (expr × bool) := p.2.rewrites.reverse.map $ λ a, (rs.nth a.1).iget,
  list.mfoldl (λ e : unit, λ q : expr × bool, rewrite_target q.1 {symm := q.2, md := semireducible}) unit.star rhs_rewrites,
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)
  .

meta def pp_rules (rs : list (expr × bool)) : tactic (list string) := rs.mmap (λ p, (do pp ← pretty_print p.1, return (if p.2 then ("←" ++ pp) else pp)))

meta def rewrite_search_target (rs : list (expr × bool)) (cfg : rewrite_search_config := {}) : tactic string :=
do t ← target,
   match t with
   | `(%%lhs = %%rhs) := do
      if cfg.trace_goal then do
        t_pp ← pretty_print t,
        trace ("rewrite_search goal: " ++ t_pp)
      else skip,
      if cfg.trace_rules then
        do rs_strings ← pp_rules rs,
          trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
      else skip,
      (steps, remaining, r1, r2) ← rewrite_search rs cfg lhs rhs,
      if cfg.trace then trace "rewrite_search found proof:" else skip,
      prf2 ← mk_eq_symm r2.proof,
      prf ← mk_eq_trans r1.proof prf2,
      if cfg.trace then trace prf else skip,
      rs_strings ← pp_rules rs,
      explanation ← (do 
        needs_refl ← check_if_simple_rewrite_succeeds rs (r1, r2),
        return (explain_proof_concisely rs_strings (r1, r2) needs_refl)) <|> return (explain_proof rs_strings (r1, r2)),
      if cfg.trace_result then trace explanation          
      else skip,
      if cfg.trace_summary then 
        do name ← decl_name,
          trace format!"during elaboration of {name}, rewrite_search (saw, searched, used) ({steps+remaining}, {steps}, {r1.rewrites.length + r2.rewrites.length}) rewrites"
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

-- meta def mk_app_aux : expr → expr → expr → tactic expr
--  | f (expr.pi n binder_info.default d b) arg := do
--    infer_type arg >>= unify d,
--    return $ f arg
--  | f (expr.pi n _ d b) arg := do
--    v ← mk_meta_var d,
--    t ← whnf (b.instantiate_var v),
--    mk_app_aux (f v) t arg
--  | e _ _ := failed

-- meta def mk_app' (f arg : expr) : tactic expr :=
-- do --trace f, trace arg,
--    t ← infer_type f >>= whnf,
--    mk_app_aux f t arg

-- meta def apps (e : expr) (F : list expr) : tactic (list expr) :=
-- -- lock_tactic_state $
-- do l ← F.mmap $ λ f, (do r ← try_core (mk_app' e f), return r.to_list), return l.join

-- meta def pairwise_apps (E F : list expr) : tactic (list expr) :=
-- (E.mmap $ λ e, apps e F) >>= λ l, return l.join

-- meta def close_under_apps_aux : list expr → list expr → tactic (list expr) 
-- | old []  := return old
-- | old new := do oldnew ← pairwise_apps old new,
--                 newold ← pairwise_apps new old,
--                 newnew ← pairwise_apps new new,
--                 close_under_apps_aux (old ++ new) (oldnew ++ newold ++ newnew)

-- meta def close_under_apps (E : list expr) : tactic (list expr) := close_under_apps_aux [] E

meta def is_eq_after_binders : expr → bool
| (expr.pi n bi d b) := is_eq_after_binders b
| `(%%a = %%b)       := tt
| _                  := ff

meta def rewrite_search_using (a : name) (cfg : rewrite_search_config := {}) : tactic string :=
do tgt ← target,
   if tgt.has_meta_var then
     fail "rewrite_search is not suitable for goals containing metavariables"
   else skip,
   names ← attribute.get_instances a,
   exprs ← names.mmap $ mk_const,
   hyps ← local_context,
   let exprs := exprs ++ hyps,
  --  rules ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas
   let rules := exprs,
   rules ← rules.mfilter $ λ r, (do t ← infer_type r, return (is_eq_after_binders t)),
   let pairs := rules.map (λ e, (e, ff)) ++ rules.map (λ e, (e, tt)),
   rewrite_search_target pairs cfg

end tactic.interactive

meta def search_attribute : user_attribute := {
  name := `search,
  descr := ""
}

run_cmd attribute.register `search_attribute

-- structure cat :=
--   (O : Type)
--   (H : O → O → Type)
--   (i : Π o : O, H o o)
--   (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
--   (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
--   (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
--   (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

-- attribute [search] cat.li cat.a

-- private example (C : cat) (X Y Z : C.O) (f : C.H X Y) (g : C.H Y X) (w : C.c g f = C.i Y) (h k : C.H Y Z) (p : C.c f h = C.c f k) : h = k := 
-- begin
-- rewrite_search_using `search {trace := tt, trace_rules:=tt},
-- end


-- PROJECT cache all_rewrites_list?
