import data.list
import data.option

import tidy.lib
import tidy.pretty_print
import tidy.rewrite_all

open tactic

namespace tidy.rewrite_search

inductive how
| rewrite : Π (rule_index : ℕ), Π (side : side), Π (location : ℕ), how
| defeq

meta inductive search_result
| success : Π proof : expr,  Π steps : list how, search_result
| failure : Π message : string, search_result

-- meta def bound_numeric := ℕ
inductive bound_progress (β : Type)
| exactly : ℕ → β → bound_progress
| at_least : ℕ → β → bound_progress

open bound_progress

def bound_progress.bound {β : Type} : bound_progress β → ℕ
| (exactly n _)  := n
| (at_least n _) := n
def bound_progress.sure {β : Type} : bound_progress β → bool
| (exactly _ _)  := tt
| (at_least _ _) := ff
def bound_progress.to_string {β : Type} : bound_progress β → string
| (exactly n _)  := "= " ++ to_string n
| (at_least n _) := "≥ " ++ to_string n

def vertex_ref : Type := ℕ
def vertex_ref_from_nat (r : ℕ) : vertex_ref := r
def vertex_ref.to_nat (r : vertex_ref) : ℕ := r
def vertex_ref.to_string (r : vertex_ref) : string := to_string r.to_nat
def vertex_ref.next (r : vertex_ref) : vertex_ref := vertex_ref_from_nat (r + 1)
def mk_vertex_ref_null : vertex_ref := vertex_ref_from_nat 0x8FFFFFFF
def mk_vertex_ref_first : vertex_ref := vertex_ref_from_nat 0

meta structure edge :=
(f t   : vertex_ref)
(proof : expr)
(how   : how)

meta structure vertex :=
(id      : vertex_ref)
(exp     : expr)
(pp      : string)
(tokens  : list string)
(root    : bool)
(visited : bool)
(s       : side)
(parent  : option edge)
(adj     : list edge)

meta def vertex.same_side (a b : vertex) : bool := a.s = b.s
meta def vertex.to_string (v : vertex) : string := v.s.to_string ++ v.pp

meta def null_expr : expr := default expr
meta def mk_null_vertex : vertex :=
⟨ mk_vertex_ref_null, null_expr, "__NULLEXPR", [], ff, ff, side.L, none, [] ⟩

structure dist_estimate (state_type : Type) :=
  (l r : vertex_ref)
  (bnd : bound_progress state_type)

def dist_estimate.side {α : Type} (de : dist_estimate α) (s : side) : vertex_ref :=
match s with
| side.L := de.l
| side.R := de.r
end

def dist_estimate.to_string {α : Type} (de : dist_estimate α) : string :=
(de.l.to_string) ++ "-" ++ (de.r.to_string) ++ "Δ" ++ de.bnd.to_string

meta def init_bound_fn (β : Type) := vertex → vertex → bound_progress β
meta def improve_estimate_fn (β : Type) := ℕ → vertex → vertex → bound_progress β → bound_progress β

meta inductive status
| going : ℕ → status
| done : edge → status
| abort : string → status
meta def status.next_itr : status → status
| (status.going n) := status.going (n + 1)
| other := other

meta structure global_state (α β : Type) :=
(next_id  : vertex_ref)
(vertices : list vertex) -- FIXME use array

(estimates : list (dist_estimate β))
(interesting_pairs : list (dist_estimate β))

(solving_edge : option edge)
(internal_strat_state : α)

namespace global_state
variables {α β : Type} (g : global_state α β)

meta def mutate_strategy (new_state : α) : global_state α β :=
{ g with internal_strat_state := new_state }

-- Retrieve the vertex with the given ref, or the null vertex if it is not
-- present.
meta def get_vertex (r : vertex_ref) : vertex :=
list.at mk_null_vertex g.vertices r

meta def set_vertex (v : vertex) : (global_state α β) :=
{ g with vertices := list.set_at g.vertices v.id v }

meta def get_endpoints (e : edge) : vertex × vertex :=
(g.get_vertex e.f, g.get_vertex e.t)

meta def get_estimate_verts (de : dist_estimate β) : vertex × vertex :=
(g.get_vertex de.l, g.get_vertex de.r)
  
-- Forcibly add a new vertex to the vertex table. Probably should never be 
-- called by a strategy and add_vertex to should used instead.
meta def do_alloc_vertex (e : expr) (root : bool) (s : side) : tactic (global_state α β × vertex) :=
do (pp, tokens) ← tokenise_expr e,
   let v : vertex := ⟨ g.next_id, e, pp, tokens, root, ff, s, none, [] ⟩,
   return ({ g with next_id := g.next_id.next, vertices := g.vertices.append [v] }, v)
  
-- Forcibly add a new pair to the interesting pair list. Probably should never be 
-- called by a strategy and add_vertex to should used instead.
meta def do_alloc_pair (de : dist_estimate β) : global_state α β :=
{g with estimates := g.estimates.append [de], interesting_pairs := g.interesting_pairs.append [de]}

meta def remove_interesting_pair (de : dist_estimate β) : global_state α β :=
let new := g.interesting_pairs.erase_such_that (λ de', de'.l = de.l ∧ de'.r = de.r) in
{g with interesting_pairs := new}

private meta def find_vertex_aux (pp : string) : list vertex → option vertex
| [] := none
| (a :: rest) := if a.pp = pp then some a else find_vertex_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← pretty_print e,
  return (find_vertex_aux pp g.vertices)

private meta def find_pair_aux {β : Type} (l r : vertex_ref) : list (dist_estimate β) → option (dist_estimate β)
| [] := none
| (a :: rest) :=
  if (a.l = l ∧ a.r = r) ∨ (a.l = r ∧ a.r = l) then
    some a
  else
    find_pair_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def find_pair (l r : vertex_ref) : option (dist_estimate β) :=
find_pair_aux l r g.estimates

meta def register_solved (e : edge) : global_state α β :=
{ g with solving_edge := some e }

meta def add_adj (v : vertex) (e : edge) : global_state α β × vertex :=
let v : vertex := { v with adj := v.adj.append [e] } in (g.set_vertex v, v)

meta def publish_parent (f t : vertex) (e : edge) : global_state α β × vertex :=
if t.root then
  (g, t)
else
  match t.parent with
  | some parent := (g, t)
  | none := let t : vertex := { t with parent := some e } in (g.set_vertex t, t)
  end

meta def mark_vertex_visited (vr : vertex_ref) : global_state α β := g.set_vertex { g.get_vertex vr with visited := tt}

-- updates rival's estimate trying to beat candidate's estimate, stopping if we do or we can't
-- go any further. We return true if we were able to beat candidate.
private meta def try_to_beat (fn : improve_estimate_fn β) (candidate rival : bound_progress β) (rival_l rival_r : vertex) : bound_progress β × bool :=
let m := candidate.bound in
match rival with
| exactly n _ := (rival, n <= m)
| at_least n p :=
  let attempt := fn m rival_l rival_r rival in
  (attempt, attempt.bound < m)
end

-- First is closer
private meta def sort_most_interesting (fn : improve_estimate_fn β) : dist_estimate β → dist_estimate β → dist_estimate β × dist_estimate β
| a b := do
match try_to_beat fn a.bnd b.bnd (g.get_vertex b.l) (g.get_vertex b.r) with
  -- b is guarenteed closer, so return it:
  | (new_b, tt) := ({ b with bnd := new_b }, a)
  -- otherwise:
  | (new_b, ff) := match a.bnd with
    -- b is further than the current estimate for a and the estimate for a is exact:
    | exactly k _  := (a, { b with bnd := new_b })
    -- or, b is futher than the current estimate for a but a might actually be worse, so check:
    | at_least k p := sort_most_interesting { b with bnd := new_b } a
  end
end

private meta def find_most_interesting_aux (fn : improve_estimate_fn β) : dist_estimate β → list (dist_estimate β) → list (dist_estimate β) → dist_estimate β × list (dist_estimate β)
| current_best seen [] := (current_best, seen)
| current_best seen (a :: rest) :=
  let (better, worse) := sort_most_interesting g fn current_best a in
  find_most_interesting_aux better (worse :: seen) rest

meta def find_most_interesting (fn : improve_estimate_fn β) : global_state α β :=
match g.interesting_pairs with
| [] := g
| (a :: rest) :=
  let (best, others) := find_most_interesting_aux g fn a [] rest in
  { g with interesting_pairs := (best :: others) }
end

end global_state

meta def refresh_fn (α β : Type) : Type :=
global_state α β → global_state α β

meta inductive strategy_action {α β : Type}
| examine : dist_estimate β → strategy_action
| refresh : refresh_fn α β → strategy_action
| abort   : string → strategy_action
  
open strategy_action

meta def step_fn (α β : Type) : Type := global_state α β → ℕ → global_state α β × (@strategy_action α β)

meta structure strategy (α β : Type) :=
(init : α)
(step : step_fn α β)

(init_bound : init_bound_fn β)
(improve_estimate_over : improve_estimate_fn β)

inductive init_result (α : Type)
| success : α → init_result
| failure : string → init_result

meta structure tracer (γ : Type) :=
(init             : tactic (init_result γ))
(publish_vertex   : γ → vertex → tactic unit)
(publish_edge     : γ → edge → tactic unit)
(publish_pair     : γ → vertex_ref → vertex_ref → tactic unit)
(publish_visited  : γ → vertex → tactic unit)
(publish_finished : γ → list edge → tactic unit)
(dump             : γ → string → tactic unit)
(pause            : γ → tactic unit)

meta structure tracer_state (γ : Type) :=
(tr       : tracer γ)
(internal : γ)

-- FIXME doesn't `unify` do exactly this??
meta def attempt_refl (lhs rhs : expr) : tactic expr :=
lock_tactic_state $
do
  gs ← get_goals,
  m ← to_expr ``(%%lhs = %%rhs) >>= mk_meta_var,
  set_goals [m],
  refl ← mk_const `eq.refl,
  tactic.apply_core refl {new_goals := new_goals.non_dep_only},
  instantiate_mvars m

meta def pick_default_tracer   : tactic unit := `[exact tidy.rewrite_search.tracer.unit_tracer]
meta def pick_default_strategy : tactic unit := `[exact tidy.rewrite_search.strategy.edit_distance_strategy]

meta structure config (α β γ : Type) extends rewrite_all_cfg :=
(strategy      : strategy α β . pick_default_strategy)
(view          : tracer γ     . pick_default_tracer)
(trace         : bool := ff)
(trace_summary : bool := ff)
(trace_result  : bool := ff)
(exhaustive    : bool := ff)

meta structure inst (α β γ : Type) :=
(conf     : config α β γ)
(rs       : list (expr × bool))
(g        : global_state α β)
(tr_state : γ)

namespace inst
variables {α β γ : Type} (i : inst α β γ)

meta def mutate (g : global_state α β) : inst α β γ:=
{ i with g := g}

meta def trace {δ : Type} [has_to_tactic_format δ] (s : δ) : tactic unit :=
if i.conf.trace then
  tactic.trace s
else
  tactic.skip

meta def tracer_vertex_added (v : vertex) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   i.trace format!"addV({v.id.to_string}): {v.pp}",
   i.conf.view.publish_vertex i.tr_state v

meta def tracer_edge_added (e : edge) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   i.trace format!"addE: {e.f.to_string}→{e.t.to_string}",
   i.conf.view.publish_edge i.tr_state e

meta def tracer_pair_added (l r : vertex_ref) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   i.trace format!"addP: {l.to_string}→{r.to_string}",
   i.conf.view.publish_pair i.tr_state l r

meta def tracer_dump {δ : Type} [has_to_tactic_format δ] (s : δ) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   fmt ← has_to_tactic_format.to_tactic_format s,
   str ← pure (to_string fmt),
   i.trace str,
   i.conf.view.dump i.tr_state str

meta def tracer_visited (v : vertex) : tactic unit :=
i.conf.view.publish_visited i.tr_state v

meta def tracer_search_finished (es : list edge) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   i.trace format!"DONE!",
   i.conf.view.publish_finished i.tr_state es

meta def dump_rws : list (expr × expr × ℕ × ℕ) → tactic unit
| [] := tactic.skip
| (a :: rest) := do tactic.trace format!"→{a.1}\nPF:{a.2}", dump_rws rest

meta def dump_vertices : list vertex → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    let pfx : string := match a.parent with
      | none := "?"
      | some p := p.f.to_string
    end,
    tracer_dump i (to_string format!"V{a.id.to_string}:{a.pp}<-{pfx}:{a.root}"),
    dump_vertices rest

meta def dump_edges : list edge → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    let (vf, vt) := i.g.get_endpoints a,
    tracer_dump i format!"E:{vf.pp}→{vt.pp}",
    dump_edges rest

meta def dump_estimates : list (dist_estimate β) → tactic unit
| [] := tactic.trace ""
| (a :: rest) := do
    tracer_dump i format!"I{(i.g.get_vertex a.l).pp}-{(i.g.get_vertex a.r).pp}:{a.bnd.bound}",
    dump_estimates rest

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def add_vertex_aux (e : expr) (root : bool) (s : side) : tactic (inst α β γ × vertex) :=
do maybe_v ← i.g.find_vertex e,
   match maybe_v with
   | none := do
     (g, v) ← i.g.do_alloc_vertex e root s,
     tracer_vertex_added i v,
     return (i.mutate g, v)
   | (some v) := return (i, v)
   end

meta def add_vertex (e : expr) (s : side) :=
i.add_vertex_aux e ff s

meta def add_root_vertex (e : expr) (s : side) :=
i.add_vertex_aux e tt s

meta def add_edge (f t : vertex) (proof : expr) (how : how) : tactic (inst α β γ × edge) :=
do let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
   tracer_edge_added i new_edge,
   let g := i.g,
   let (g, f) := g.add_adj f new_edge,
   let (g, t) := g.add_adj t new_edge,
   let (g, t) := g.publish_parent f t new_edge,
   if ¬(vertex.same_side f t) then
     return (i.mutate (g.register_solved new_edge), new_edge)
   else
     return (i.mutate g, new_edge)

-- Add an "interesting pair" to the global state
meta def add_pair (l r : vertex) : tactic (inst α β γ) :=
do tracer_pair_added i l.id r.id,
   match i.g.find_pair l.id r.id with
   | some de := return i
   | none    := return (i.mutate (i.g.do_alloc_pair ⟨ l.id, r.id, i.conf.strategy.init_bound l r ⟩))
   end

meta def remove_interesting_pair (de : dist_estimate β) : inst α β γ :=
i.mutate (i.g.remove_interesting_pair de)

meta def find_most_interesting : inst α β γ :=
i.mutate (i.g.find_most_interesting i.conf.strategy.improve_estimate_over)

meta def process_new_rewrites (f : vertex) : inst α β γ → list (expr × expr × how) → tactic (inst α β γ × list vertex × list edge)
| i [] := return (i, [], [])
| i ((new_expr, prf, how) :: rest) := do
    (i, v) ← i.add_vertex new_expr f.s,
    (i, e) ← i.add_edge f v prf how,
    (i, vs, es) ← process_new_rewrites i rest,
    return (i, (v :: vs), (e :: es))

meta def add_new_interestings (v : vertex) : inst α β γ → list vertex → tactic (inst α β γ)
| i [] := return i
| i (a :: rest) := do
    i ← i.add_pair v a,
    add_new_interestings i rest

/-- Check if `eq.refl _` suffices to prove the two sides are equal. -/
meta def unify (de : dist_estimate β) : tactic (inst α β γ) :=
do
  let (lhs, rhs) := i.g.get_estimate_verts de,
  prf ← attempt_refl lhs.exp rhs.exp,
  -- success! we're done
  (i, _) ← i.add_edge lhs rhs prf how.defeq,
  return i

meta def find_neighbours (v : vertex) : tactic ((inst α β γ) × (list vertex)) :=
do
  match v.visited with
  | tt := do
            let vertices := v.adj.map (λ e, i.g.get_vertex e.t),
            return (i, vertices)
  | ff := do
            all_rws ← all_rewrites_list i.rs ff v.exp i.conf.to_rewrite_all_cfg,
            let all_rws := all_rws.map (λ t, (t.1, t.2.1, how.rewrite t.2.2.1 v.s t.2.2.2)),
            (i, adjacent_vertices, _) ← i.process_new_rewrites v all_rws,
            i ← pure (i.mutate (i.g.mark_vertex_visited v.id)),
            i.tracer_visited v,
            return (i, adjacent_vertices)
  end

-- My job is to examine the specified vertex and blow it up
meta def examine_one (de : dist_estimate β) (s : side) : tactic (inst α β γ) :=
do
  let v := i.g.get_vertex (de.side s),
  (i, nbhd) ← i.find_neighbours v,
  i ← i.add_new_interestings (i.g.get_vertex (de.side s.other)) nbhd,
  return i

meta def examine_both (de : dist_estimate β) : tactic (inst α β γ ) :=
do
  i ← i.examine_one de side.L,
  i ← i.examine_one de side.R,
  i ← pure (i.remove_interesting_pair de), -- FIXME this feels a bit silly: isn't `de` always the head of the list?
  i ← pure i.find_most_interesting,
  return i

meta def step_once (itr : ℕ) : tactic (inst α β γ × status) :=
match i.g.solving_edge with
| some e := return (i, status.done e)
| none :=
  let (g, action) := i.conf.strategy.step i.g itr in
  let i := i.mutate g in
  match action with 
  | examine de := do
    (lhs, rhs) ← pure (g.get_estimate_verts de),
    i.trace format!"examine({lhs.id.to_nat}, {rhs.id.to_nat}) distance {de.bnd.to_string}: ({lhs.pp}) = ({rhs.pp})",
    i ← (i.unify de) <|> (i.examine_both de),
    return (i, status.going (itr + 1))
  | refresh ref_fn := do
    i.trace format!"refresh",
    return (i.mutate (ref_fn i.g), status.going (itr + 1))
  | abort reason := do
    i.trace format!"abort: {reason}",
    return (i, status.abort reason)
  end
end

-- Find a vertex we haven't visited, and visit it. The bool is true if there might
-- be any more unvisited vertices.
meta def exhaust_one : list vertex → tactic (inst α β γ × bool)
| []          := return (i, ff)
| (v :: rest) :=
  if v.visited then
    exhaust_one rest
  else do
    (i, _) ← i.find_neighbours v,
    return (i, tt)

meta def exhaust_all : inst α β γ → tactic (inst α β γ) := λ i, do
  (i, more_left) ← i.exhaust_one i.g.vertices,
  if more_left then i.exhaust_all else return i

meta def backtrack : vertex → option edge → tactic (option expr × list edge)
| v e := match e with
       | none := return (none, [])
       | (some e) := do 
                      let w : vertex := i.g.get_vertex e.f,
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
  let (from_vertex, to_vertex) := i.g.get_endpoints e,

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
  i.tracer_search_finished edges,

  i.trace from_vertex.to_string,
  i.trace to_vertex.to_string,

  if i.conf.trace_summary then do
    let saw := i.g.vertices.length,
    let visited := (i.g.vertices.filter (λ v : vertex, v.visited)).length,
    name ← decl_name,
    tactic.trace format!"rewrite_search (saw/visited/used) {saw}/{visited}/{edges.length} expressions during proof of {name}"
  else 
    skip,

  i ← if i.conf.exhaustive then i.exhaust_all else pure i,

  return (proof, edges)

meta def search_until_abort_aux : inst α β γ → ℕ → tactic search_result
| i itr := do
  (i, s) ← i.step_once itr,
  match s with
  | status.going k := search_until_abort_aux i (itr + 1)
  | status.abort r := return (search_result.failure ("aborted: " ++ r))
  | status.done e  := do
    (proof, edges) ← i.solve_goal e,
    return (search_result.success proof (edges.map edge.how))
  end

meta def search_until_abort : tactic search_result :=
do
  res ← i.search_until_abort_aux 0,
  return res

end inst

end tidy.rewrite_search
