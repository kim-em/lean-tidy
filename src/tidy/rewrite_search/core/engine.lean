import data.list
import data.option
import tidy.pretty_print
import tidy.rewrite_all

import .types
import .debug

open tactic

universe u

namespace tidy.rewrite_search

namespace search_state
variables {α β γ δ : Type} (g : search_state α β γ δ)

meta def reset_estimate (init : init_bound_fn α β γ δ) (de : dist_estimate γ) : tactic (dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  return de

meta def reset_all_estimates (init : init_bound_fn α β γ δ) : tactic (search_state α β γ δ) := do
  new_estimates ← g.estimates.mmap (g.reset_estimate init),
  return { g with estimates := new_estimates }

private def register_tokens_aux (s : side) : table token → list string → table token × list table_ref
| tokens [] := (tokens, [])
| tokens (tstr :: rest) := do
  let (tokens, t) := find_or_create_token tokens s tstr,
  let (tokens, l) := register_tokens_aux tokens rest,
  (tokens, t.id :: l)

meta def register_tokens (s : side) (strs : list string) : search_state α β γ δ × list table_ref :=
  let (new_tokens, refs) := register_tokens_aux s g.tokens strs in
  ({g with tokens := new_tokens}, refs)

private meta def find_vertex_aux (pp : string) : list vertex → option vertex
| [] := none
| (a :: rest) := if a.pp = pp then some a else find_vertex_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← pretty_print e,
  return (g.vertices.find_key pp)

-- Forcibly add a new vertex to the vertex table. You probably actually want to call
-- add_vertex, which will check that we haven't seen the vertex before first.
meta def alloc_vertex (e : expr) (root : bool) (s : side) : tactic (search_state α β γ δ × vertex) :=
do (pp, tokens) ← tokenise_expr e,
   let (g, token_refs) := g.register_tokens s tokens,
   let v : vertex := ⟨ g.vertices.next_id, e, pp, token_refs, root, ff, s, none, [] ⟩,
   return ({ g with vertices := g.vertices.alloc v }, v)

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def add_vertex_aux (e : expr) (root : bool) (s : side) : tactic (search_state α β γ δ × vertex) :=
do maybe_v ← g.find_vertex e,
   match maybe_v with
   | none := do
     (g, v) ← g.alloc_vertex e root s,
     g.tracer_vertex_added v,
     return (g, v)
   | (some v) := return (g, v)
   end

meta def add_vertex (e : expr) (s : side) :=
g.add_vertex_aux e ff s

meta def add_root_vertex (e : expr) (s : side) :=
g.add_vertex_aux e tt s

meta def register_solved (e : edge) : search_state α β γ δ :=
{ g with solving_edge := some e }

meta def add_adj (v : vertex) (e : edge) : search_state α β γ δ × vertex :=
let v : vertex := { v with adj := v.adj.concat e } in (g.set_vertex v, v)

meta def publish_parent (f t : vertex) (e : edge) : search_state α β γ δ × vertex :=
if t.root then
  (g, t)
else
  match t.parent with
  | some parent := (g, t)
  | none := let t : vertex := { t with parent := some e } in (g.set_vertex t, t)
  end

meta def mark_vertex_visited (r : table_ref) : tactic (search_state α β γ δ) := do
  v ← g.vertices.get r,
  return $ g.set_vertex { v with visited := tt }

meta def add_edge (f t : vertex) (proof : expr) (how : how) : tactic (search_state α β γ δ × edge) :=
do let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
   g.tracer_edge_added new_edge,
   let (g, f) := g.add_adj f new_edge,
   let (g, t) := g.add_adj t new_edge,
   let (g, t) := g.publish_parent f t new_edge,
   if ¬(vertex.same_side f t) then
     return (g.register_solved new_edge, new_edge)
   else
     return (g, new_edge)

meta def process_new_rewrites (f : vertex) : search_state α β γ δ → list (expr × expr × how) → tactic (search_state α β γ δ × list vertex × list edge)
| g [] := return (g, [], [])
| g ((new_expr, prf, how) :: rest) := do
    (g, v) ← g.add_vertex new_expr f.s,
    (g, e) ← g.add_edge f v prf how,
    (g, vs, es) ← process_new_rewrites g rest,
    return (g, (v :: vs), (e :: es))

meta def visit_vertex (v : vertex) : tactic (search_state α β γ δ × list vertex) :=
do
  match v.visited with
  | tt := do
            vertices ← v.adj.mmap (λ e, g.vertices.get e.t),
            return (g, vertices)
  | ff := do
            all_rws ← all_rewrites_list g.conf.rs ff v.exp g.conf.to_rewrite_all_cfg,
            let all_rws := all_rws.map (λ t, (t.1, t.2.1, how.rewrite t.2.2.1 v.s t.2.2.2)),
            (g, adjacent_vertices, _) ← g.process_new_rewrites v all_rws,
            g ← g.mark_vertex_visited v.id,
            g.tracer_visited v,
            return (g, adjacent_vertices)
  end

meta def improve_estimate_over {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (threshold : ℚ) (de : dist_estimate γ) : tactic (search_state α β γ δ × dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  let new_bnd := m.improve_estimate_over g threshold vl vr de.bnd,
  let new_de := {de with bnd := new_bnd},
  return ({g with estimates := g.estimates.update new_de}, new_de)

meta def alloc_estimate {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (p : pair) : tactic (search_state α β γ δ × table_ref) := do
  (vl, vr) ← g.lookup_pair p,
  let ref := g.estimates.next_id,
  let new_estimates := g.estimates.alloc ⟨p, ref, m.init_bound g vl vr⟩,
  return ({g with estimates := new_estimates}, ref)

/-- Check if `eq.refl _` suffices to prove the two sides are equal. -/
meta def unify (p : pair) : tactic (search_state α β γ δ) :=
do
  (lhs, rhs) ← g.lookup_pair p,
  prf ← attempt_refl lhs.exp rhs.exp,
  -- success! we're done
  (g, _) ← g.add_edge lhs rhs prf how.defeq,
  return g

end search_state

namespace inst
variables {α β γ δ : Type} (i : inst α β γ δ)

meta def mutate (g : search_state α β γ δ) : inst α β γ δ :=
{ i with g := g }

meta def step_once (itr : ℕ) : tactic (inst α β γ δ × status) :=
match i.g.solving_edge with
| some e := return (i, status.done e)
| none := do
  if itr > i.g.conf.max_iterations then
    return (i, status.abort "max iterations reached!")
  else do
    g ← i.metric.update i.g itr,
    (g, s) ← i.strategy.step g i.metric itr,
    return (i.mutate g, s)
end

-- Find a vertex we haven't visited, and visit it. The bool is true if there might
-- be any more unvisited vertices.
meta def exhaust_one : list vertex → tactic (inst α β γ δ × bool)
| []          := return (i, ff)
| (v :: rest) :=
  if v.visited then
    exhaust_one rest
  else do
    (g, _) ← i.g.visit_vertex v,
    return (i.mutate g, tt)

meta def exhaust_all : inst α β γ δ → tactic (inst α β γ δ) := λ i, do
  (i, more_left) ← i.exhaust_one i.g.vertices.to_list,
  if more_left then i.exhaust_all else return i

meta def backtrack : vertex → option edge → tactic (option expr × list edge)
| v e := match e with
       | none := return (none, [])
       | (some e) := do
                      w ← i.g.vertices.get e.f,
                      (prf_o, edges) ← backtrack w w.parent,
                      match prf_o with
                      | none := return (some e.proof, [e])
                      | (some prf) := do new_prf ← tactic.mk_eq_trans prf e.proof,
                                          return (some new_prf, e :: edges)
                      end
       end

meta def combine_proofs : option expr → option expr → tactic expr
| none     none     := fail "unreachable code!"
| (some a) none     := return a
| none     (some b) := mk_eq_symm b
| (some a) (some b) := do b' ← mk_eq_symm b, mk_eq_trans a b'

meta def solve_goal (e : edge) : tactic (expr × list edge) :=
do
  (from_vertex, to_vertex) ← i.g.get_endpoints e,

  (from_prf, from_edges) ← i.backtrack to_vertex e,
  (to_prf, to_edges) ← i.backtrack to_vertex to_vertex.parent,

  proof ← match from_vertex.s with
           | side.L := combine_proofs from_prf to_prf
           | side.R := combine_proofs to_prf from_prf
           end,

  let edges := match from_vertex.s with
               | side.L := (to_edges ++ from_edges).reverse
               | side.R := (from_edges ++ to_edges).reverse
               end,

  -- This must be called before i.exhaust_all
  i.g.tracer_search_finished edges,

  i.g.trace from_vertex.to_string,
  i.g.trace to_vertex.to_string,

  if i.g.conf.trace_summary then do
    let vl := i.g.vertices.to_list,
    let saw := vl.length,
    let visited := (vl.filter (λ v : vertex, v.visited)).length,
    name ← decl_name,
    tactic.trace format!"rewrite_search (saw/visited/used) {saw}/{visited}/{edges.length} expressions during proof of {name}"
  else
    skip,

  i ← if i.g.conf.exhaustive then i.exhaust_all else pure i,

  return (proof, edges)

meta def search_until_solved_aux : inst α β γ δ → ℕ → tactic search_result
| i itr := do
  (i, s) ← i.step_once itr,
  match s with
  | status.continue := search_until_solved_aux i (itr + 1)
  | status.repeat   := search_until_solved_aux i itr
  | status.abort r  := return (search_result.failure ("aborted: " ++ r))
  | status.done e   := do
    (proof, edges) ← i.solve_goal e,
    return $ search_result.success proof (edges.map edge.how)
  end

meta def search_until_solved : tactic search_result := i.search_until_solved_aux 0

end inst

end tidy.rewrite_search
