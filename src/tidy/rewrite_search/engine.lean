import data.list
import data.option

import .table

import tidy.lib
import tidy.pretty_print
import tidy.rewrite_all

open tactic

universe u

namespace tidy.rewrite_search

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

inductive how
| rewrite (rule_index : ℕ) (side : side) (location : ℕ) : how
| defeq

meta inductive search_result
| success (proof : expr) (steps : list how) : search_result
| failure (message : string) : search_result

-- meta def bound_numeric := ℕ
inductive bound_progress (β : Type u)
| exactly : ℚ → β → bound_progress
| at_least : ℚ → β → bound_progress

open bound_progress

def bound_progress.bound {β : Type u} : bound_progress β → ℚ
| (exactly n _)  := n
| (at_least n _) := n
def bound_progress.sure {β : Type u} : bound_progress β → bool
| (exactly _ _)  := tt
| (at_least _ _) := ff
def bound_progress.to_string {β : Type u} : bound_progress β → string
| (exactly n _)  := "= " ++ to_string n
| (at_least n _) := "≥ " ++ to_string n

meta structure edge :=
(f t   : table_ref)
(proof : expr)
(how   : how)

structure token :=
(id                : table_ref)
(str               : string)
(lhs_freq rhs_freq : ℕ)
def token.inc (t : token) : side → token
| side.L := { t with lhs_freq := t.lhs_freq + 1}
| side.R := { t with rhs_freq := t.rhs_freq + 1}
def token.freq (t : token) : side → ℕ
| side.L := t.lhs_freq
| side.R := t.rhs_freq

def null_token : token :=
⟨ null_table_ref, "__NULLTOKEN", 0, 0 ⟩

instance token.inhabited : inhabited token := ⟨null_token⟩
instance token.indexed : indexed token := ⟨λ t, t.id⟩
instance token.keyed : keyed token string := ⟨λ v, v.str⟩

def find_or_create_token (tokens : table token) (s : side) (tstr : string) : table token × token :=
match tokens.find tstr with
| none := do
  let t : token := ⟨tokens.next_id, tstr, 0, 0⟩,
  let t := t.inc s in (tokens.alloc t, t)
| (some t) := do
  let t := t.inc s in (tokens.update t, t)
end

meta structure vertex :=
(id      : table_ref)
(exp     : expr)
(pp      : string)
(tokens  : list table_ref)
(root    : bool)
(visited : bool)
(s       : side)
(parent  : option edge)
(adj     : list edge)

meta def vertex.same_side (a b : vertex) : bool := a.s = b.s
meta def vertex.to_string (v : vertex) : string := v.s.to_string ++ v.pp

meta def null_expr : expr := default expr
meta def null_vertex : vertex :=
⟨ null_table_ref, null_expr, "__NULLEXPR", [], ff, ff, side.L, none, [] ⟩

meta instance vertex.inhabited : inhabited vertex := ⟨null_vertex⟩
meta instance vertex.indexed : indexed vertex := ⟨λ v, v.id⟩
meta instance vertex.keyed : keyed vertex string := ⟨λ v, v.pp⟩
meta instance vertex.has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩

@[derive decidable_eq]
structure pair :=
  (l r : table_ref)
def pair.side (p : pair) (s : side) : table_ref :=
match s with
| side.L := p.l
| side.R := p.r
end
def pair.flip (p : pair) : pair := ⟨p.r, p.l⟩
def pair.to_string (c : pair) : string :=
  (c.l.to_string) ++ "-" ++ (c.r.to_string)
instance pair.has_to_string : has_to_string pair := ⟨pair.to_string⟩

structure dist_estimate (state_type : Type u) extends pair :=
  (id : table_ref)
  (bnd : bound_progress state_type)
def dist_estimate.side {α : Type u} (de : dist_estimate α) (s : side) : table_ref :=
  de.to_pair.side s
def dist_estimate.to_string {α : Type u} (de : dist_estimate α) : string :=
(pair.to_string de.to_pair) ++ "Δ" ++ de.bnd.to_string
def dist_estimate.set_bound {α : Type u} (de : dist_estimate α) (bnd : bound_progress α) : dist_estimate α := { de with bnd := bnd }

instance dist_estimate.indexed {α : Type u} : indexed (dist_estimate α) := ⟨λ v, v.id⟩
instance dist_estimate.keyed {α : Type u} : keyed (dist_estimate α) pair := ⟨λ v, v.to_pair⟩

meta inductive status
| going : ℕ → status
| done : edge → status
| abort : string → status
meta def status.next_itr : status → status
| (status.going n) := status.going (n + 1)
| other := other

inductive init_result (γ : Type)
| success : γ → init_result
| failure : string → init_result

meta structure config extends rewrite_all_cfg :=
(rs            : list (expr × bool))
(trace         : bool := ff)
(trace_summary : bool := ff)
(trace_result  : bool := ff)
(exhaustive    : bool := ff)

--The unused params α, β, γ must be here in order that lean does not freak out
--when it goes to fill the moduleset with some defaults. In particular, if only
--a tracer was explicitly specified, then the autoparams would fail.
meta structure tracer (α β γ δ : Type) :=
(init             : tactic (init_result δ))
(publish_vertex   : δ → vertex → tactic unit)
(publish_edge     : δ → edge → tactic unit)
(publish_pair     : δ → table_ref → table_ref → tactic unit)
(publish_visited  : δ → vertex → tactic unit)
(publish_finished : δ → list edge → tactic unit)
(dump             : δ → string → tactic unit)
(pause            : δ → tactic unit)

meta structure search_state (α β γ δ : Type) :=
(tr           : @tracer α β γ δ)
(conf         : config)
(strat_state  : α)
(metric_state : β)
(tokens       : table token)
(vertices     : table vertex)
(estimates    : table (dist_estimate γ))
(solving_edge : option edge)
(tr_state     : δ)

meta def init_bound_fn (α β γ δ : Type) := search_state α β γ δ → vertex → vertex → bound_progress γ
meta def improve_estimate_fn (α β γ δ : Type) := search_state α β γ δ → ℚ → vertex → vertex → bound_progress γ → bound_progress γ

namespace search_state
variables {α β γ δ : Type} (g : search_state α β γ δ)

meta def mutate_strat (new_state : α) : search_state α β γ δ :=
{ g with strat_state := new_state }

meta def mutate_metric (new_state : β) : search_state α β γ δ :=
{ g with metric_state := new_state }

meta def trace {ε : Type} [has_to_tactic_format ε] (s : ε) : tactic unit :=
if g.conf.trace then tactic.trace s else tactic.skip

meta def tracer_vertex_added (v : vertex) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   g.trace format!"addV({v.id.to_string}): {v.pp}",
   g.tr.publish_vertex g.tr_state v

meta def tracer_edge_added (e : edge) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   g.trace format!"addE: {e.f.to_string}→{e.t.to_string}",
   g.tr.publish_edge g.tr_state e

meta def tracer_pair_added (l r : table_ref) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   g.trace format!"addP: {l.to_string}→{r.to_string}",
   g.tr.publish_pair g.tr_state l r

meta def tracer_dump {ε : Type} [has_to_tactic_format ε] (s : ε) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   fmt ← has_to_tactic_format.to_tactic_format s,
   str ← pure (to_string fmt),
   g.trace str,
   g.tr.dump g.tr_state str

meta def tracer_visited (v : vertex) : tactic unit :=
g.tr.publish_visited g.tr_state v

meta def tracer_search_finished (es : list edge) : tactic unit :=
do --FIXME guard all of these with an if (to prevent pointless string building)
   g.trace format!"DONE!",
   g.tr.publish_finished g.tr_state es

meta def set_vertex (v : vertex) : (search_state α β γ δ) :=
{ g with vertices := g.vertices.set v.id v }

meta def lookup_pair (p : pair) : tactic (vertex × vertex) := do
vf ← g.vertices.get p.l, vt ← g.vertices.get p.r, return (vf, vt)

meta def get_endpoints (e : edge) : tactic (vertex × vertex) := do
vf ← g.vertices.get e.f, vt ← g.vertices.get e.t, return (vf, vt)

meta def get_estimate_verts (de : dist_estimate γ) : tactic (vertex × vertex) := g.lookup_pair de.to_pair

meta def reset_dist_estimate (init : init_bound_fn α β γ δ) (de : dist_estimate γ) : tactic (dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  return de

meta def reset_all_estimates (init : init_bound_fn α β γ δ) : tactic (search_state α β γ δ) := do
  new_estimates ← g.estimates.mmap (g.reset_dist_estimate init),
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

-- Forcibly add a new vertex to the vertex table. Probably should never be
-- called by a metric and add_vertex to should used instead.
meta def do_alloc_vertex (e : expr) (root : bool) (s : side) : tactic (search_state α β γ δ × vertex) :=
do (pp, tokens) ← tokenise_expr e,
   let (g, token_refs) := g.register_tokens s tokens,
   let v : vertex := ⟨ g.vertices.next_id, e, pp, token_refs, root, ff, s, none, [] ⟩,
   return ({ g with vertices := g.vertices.alloc v }, v)

private meta def find_vertex_aux (pp : string) : list vertex → option vertex
| [] := none
| (a :: rest) := if a.pp = pp then some a else find_vertex_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← pretty_print e,
  return (g.vertices.find pp)

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

/-- Check if `eq.refl _` suffices to prove the two sides are equal. -/
meta def unify (p : pair) : tactic (search_state α β γ δ) :=
do
  (lhs, rhs) ← g.lookup_pair p,
  prf ← attempt_refl lhs.exp rhs.exp,
  -- success! we're done
  (g, _) ← g.add_edge lhs rhs prf how.defeq,
  return g

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def add_vertex_aux (e : expr) (root : bool) (s : side) : tactic (search_state α β γ δ × vertex) :=
do maybe_v ← g.find_vertex e,
   match maybe_v with
   | none := do
     (g, v) ← g.do_alloc_vertex e root s,
     g.tracer_vertex_added v,
     return (g, v)
   | (some v) := return (g, v)
   end

meta def add_vertex (e : expr) (s : side) :=
g.add_vertex_aux e ff s

meta def add_root_vertex (e : expr) (s : side) :=
g.add_vertex_aux e tt s

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

end search_state

meta def refresh_fn (α β γ δ : Type) : Type := search_state α β γ δ → tactic (search_state α β γ δ)

meta def init_fn (α : Type) : Type := α
meta def update_fn (α β γ δ : Type) : Type := search_state α β γ δ → ℕ → tactic (search_state α β γ δ)

meta structure metric (α β γ δ : Type) :=
(init : init_fn β)
(pre_step : update_fn α β γ δ)
(init_bound : init_bound_fn α β γ δ)
(improve_estimate_over : improve_estimate_fn α β γ δ)

meta def search_state.improve_estimate_over {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (threshold : ℚ) (de : dist_estimate γ) : tactic (search_state α β γ δ × dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  let new_bnd := m.improve_estimate_over g threshold vl vr de.bnd,
  let new_de := {de with bnd := new_bnd},
  return ({g with estimates := g.estimates.update new_de}, new_de)




meta def search_state.improve_estimate_over3 {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (de : dist_estimate γ) (new_bnd : bound_progress γ) : tactic (search_state α β γ δ × dist_estimate γ) := do
  let new_de := {de with bnd := new_bnd},
  return ({g with estimates := g.estimates.update new_de}, new_de)

meta def search_state.improve_estimate_over2 {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (threshold : ℚ) (vl vr : vertex) (de : dist_estimate γ) : tactic (search_state α β γ δ × dist_estimate γ) := do
  let new_bnd := m.improve_estimate_over g threshold vl vr de.bnd,
  search_state.improve_estimate_over3 g m de new_bnd

meta def search_state.improve_estimate_over1 {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (threshold : ℚ) (de : dist_estimate γ) : tactic (search_state α β γ δ × dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  search_state.improve_estimate_over2 g m threshold vl vr de




meta def search_state.alloc_estimate {α β γ δ : Type} (g : search_state α β γ δ) (m : metric α β γ δ) (p : pair) : tactic (search_state α β γ δ × table_ref) := do
  (vl, vr) ← g.lookup_pair p,
  let ref := g.estimates.next_id,
  let new_estimates := g.estimates.alloc ⟨p, ref, m.init_bound g vl vr⟩,
  return ({g with estimates := new_estimates}, ref)

meta def startup_fn (α β γ δ : Type) : Type := search_state α β γ δ → metric α β γ δ → vertex → vertex → tactic (search_state α β γ δ)
meta def step_fn (α β γ δ : Type) : Type := search_state α β γ δ → metric α β γ δ → ℕ → tactic (search_state α β γ δ × status)

meta structure strategy (α β γ δ : Type) :=
(init : init_fn α)
(startup : startup_fn α β γ δ)
(step : step_fn α β γ δ)

meta structure inst (α β γ δ : Type) :=
(metric   : metric α β γ δ)
(strategy : strategy α β γ δ)
(g        : search_state α β γ δ)

namespace inst
variables {α β γ δ : Type} (i : inst α β γ δ)

meta def mutate (g : search_state α β γ δ) : inst α β γ δ :=
{ i with g := g }

meta def dump_rws : list (expr × expr × ℕ × ℕ) → tactic unit
| [] := tactic.skip
| (a :: rest) := do tactic.trace format!"→{a.1}\nPF:{a.2}", dump_rws rest

meta def dump_tokens : list token → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    tactic.trace format!"V{a.id.to_string}:{a.str}|{a.lhs_freq}v{a.rhs_freq}",
    dump_tokens rest

meta def dump_vertices : list vertex → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    let pfx : string := match a.parent with
      | none := "?"
      | some p := p.f.to_string
    end,
    i.g.tracer_dump (to_string format!"V{a.id.to_string}:{a.pp}<-{pfx}:{a.root}"),
    dump_vertices rest

meta def dump_edges : list edge → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    (vf, vt) ← i.g.get_endpoints a,
    i.g.tracer_dump format!"E:{vf.pp}→{vt.pp}",
    dump_edges rest

meta def dump_estimates : list (dist_estimate β) → tactic unit
| [] := tactic.trace ""
| (a :: rest) := do
    lpp ← i.g.vertices.get a.l,
    rpp ← i.g.vertices.get a.r,
    i.g.tracer_dump format!"I{lpp}-{rpp}:{a.bnd.bound}",
    dump_estimates rest

meta def step_once (itr : ℕ) : tactic (inst α β γ δ × status) :=
match i.g.solving_edge with
| some e := return (i, status.done e)
| none := do
  g ← i.metric.pre_step i.g itr,
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
  | status.going k := search_until_solved_aux i (itr + 1)
  | status.abort r := return (search_result.failure ("aborted: " ++ r))
  | status.done e  := do
    (proof, edges) ← i.solve_goal e,
    return (search_result.success proof (edges.map edge.how))
  end

meta def search_until_solved : tactic search_result := i.search_until_solved_aux 0

end inst

meta def strategy_constructor (α : Type) := Π (β γ δ : Type), strategy α β γ δ
meta def metric_constructor (β γ : Type) := Π (α δ : Type), metric α β γ δ
meta def tracer_constructor (δ : Type) := Π (α β γ : Type), tracer α β γ δ

end tidy.rewrite_search
