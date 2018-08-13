import data.list
import data.option

import tidy.lib
import tidy.pretty_print
import .rewrite_all

namespace tidy.rewrite_search

inductive side
| L
| R
def side.other : side → side
| side.L := side.R
| side.R := side.L
def side.to_string : side → string
| side.L := "L"
| side.R := "R"

inductive search_result
| success : string → search_result
| failure : string → search_result

-- universe variables u v
-- Workaround for the crazy fact that you are only allowed a single universe
-- in a "do" block. (NOOOOOooooooooo......... (it's getting quieter because
-- I'm moving on with life.))
-- meta def pl {α : Type u} (a : α) : tactic (ulift α) := pure (ulift.up a)
-- meta def ul {α : Type u} {β : Type v} (a : tactic α) : tactic (ulift α) := ulift.up a

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
| (exactly n _)  := "=" ++ to_string n
| (at_least n _) := "≥" ++ to_string n

meta def tokenise_expr (e : expr) : tactic (string × list string) := do
  pp ← pretty_print e,
  pure (pp, pp.split_on ' ')

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
(how   : ℕ) -- Scott: doen't we need to store two ℕs here? which rule, and which application?

meta structure vertex :=
(id      : vertex_ref)
(exp     : expr)
(pp      : string)
(tokens  : list string)
(root    : bool)
(visited : bool)
(s       : option side) -- Scott: why is this an option?
(parent  : option edge)
(adj     : list edge)

--FIXME do this better with decidability
meta def vertex.same_side (a b : vertex) : bool :=
match (a.s, b.s) with
| (some side.L, some side.L) := tt
| (some side.R, some side.R) := tt
| _ := ff
end

meta def vertex.to_string (v : vertex) : string :=
let pfx : string := match v.s with
| (some s) := s.to_string
| none := "?"
end in
pfx ++ v.pp

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
| abort
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

-- Retrieve the vertex with the given ref, or the null vertex if it is not
-- present.
meta def get_vertex (r : vertex_ref) : vertex :=
list_at mk_null_vertex g.vertices r

meta def set_vertex (v : vertex) : (global_state α β) :=
⟨ g.next_id, list_set_at g.vertices v.id v, g.estimates, g.interesting_pairs, g.solving_edge, g.internal_strat_state ⟩

meta def get_endpoints (e : edge) : vertex × vertex :=
(g.get_vertex e.f, g.get_vertex e.t)

meta def get_estimate_verts (de : dist_estimate β) : vertex × vertex :=
(g.get_vertex de.l, g.get_vertex de.r)
  
-- Forcibly add a new vertex to the vertex table. Probably should never be 
-- called by a strategy and add_vertex to should used instead.
meta def do_alloc_vertex (e : expr) (root : bool) (s : option side)
  : tactic (global_state α β × vertex) := 
do (pp, tokens) ← tokenise_expr e,
   let v : vertex := ⟨ g.next_id, e, pp, tokens, root, ff, s, none, [] ⟩,
   return (⟨ g.next_id.next, g.vertices.append [v], g.estimates, g.interesting_pairs, g.solving_edge,g.internal_strat_state ⟩, v)
  
-- Forcibly add a new pair to the interesting pair list. Probably should never be 
-- called by a strategy and add_vertex to should used instead.
meta def do_alloc_pair (de : dist_estimate β)
  : tactic (global_state α β) := 
return (⟨ g.next_id, g.vertices, g.estimates.append [de], g.interesting_pairs.append [de], g.solving_edge, g.internal_strat_state ⟩)

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
⟨ g.next_id, g.vertices, g.estimates, g.interesting_pairs, some e, g.internal_strat_state ⟩

meta def add_adj (v : vertex) (e : edge) : tactic (global_state α β × vertex) := 
do let v : vertex := ⟨ v.id, v.exp, v.pp, v.tokens, v.root, v.visited, v.s, v.parent, v.adj.append [e] ⟩,
   return (g.set_vertex v, v)

meta def publish_parent (f t : vertex) (e : edge) : tactic (global_state α β × vertex) :=
if t.root then
  return (g, t)
else
  match t.parent with
  | some parent := return (g, t)
  | none := do
    let t : vertex := ⟨ t.id, t.exp, t.pp, t.tokens, t.root, t.visited, t.s, some e, t.adj ⟩,
    return (g.set_vertex t, t)
  end

meta def mark_vertex_visited (vr : vertex_ref) : global_state α β :=
let v := g.get_vertex vr in
g.set_vertex ⟨ v.id, v.exp, v.pp, v.tokens, v.root, tt, v.s, v.parent, v.adj ⟩

-- updates rival's estimate trying to beat candidate's estimate, stopping if we do or we can't
-- go any further. We return true if we were able to beat candidate.
private meta def try_to_beat (fn : improve_estimate_fn β) (candidate rival : bound_progress β)
  (rival_l rival_r : vertex) : bound_progress β × bool :=
  let m := candidate.bound in
  match rival with
  | exactly n _ := (rival, n <= m)
  | at_least n p :=
    let attempt := fn m rival_l rival_r rival in
    (attempt, attempt.bound < m)
  end

-- First is closer
private meta def sort_most_interesting (fn : improve_estimate_fn β)
  : dist_estimate β → dist_estimate β → tactic (dist_estimate β × dist_estimate β)
  | a b := do
  match try_to_beat fn a.bnd b.bnd (g.get_vertex b.l) (g.get_vertex b.r) with
    -- b is guarenteed closer, so return it:
    | (new_b, ff) := return (⟨ b.l, b.r, new_b ⟩, a)
    -- otherwise:
    | (new_b, tt) := match a.bnd with
      -- b is further than the current estimate for a and the estimate for a is exact:
      | exactly k _  := return (a, ⟨ b.l, b.r, new_b ⟩)
      -- or, b is futher than the current estimate for a but a might actually be worse, so check:
      | at_least k p := sort_most_interesting ⟨ b.l, b.r, new_b ⟩ a
    end
  end

private meta def find_most_interesting_aux_1 (fn : improve_estimate_fn β)
  : dist_estimate β → list (dist_estimate β) → list (dist_estimate β) → tactic (dist_estimate β × list (dist_estimate β))
  | current_best seen [] := return (current_best, seen)
  | current_best seen (a :: rest) := do
    (vl, vr) ← pure (g.get_estimate_verts a),
    -- Drop "interesting" vertices which have had both ends visited, and hence aren't interesting
    -- any more.
    if vl.visited ∧ vr.visited then
      find_most_interesting_aux_1 current_best seen rest
    else do
      (better, worse) ← sort_most_interesting g fn current_best a,
      r ← find_most_interesting_aux_1 better (worse :: seen) rest,
      return r

private meta def find_most_interesting_aux_2 (fn : improve_estimate_fn β)
  : list (dist_estimate β) → tactic (list (dist_estimate β))
  | [] := return []
  | (a :: rest) := do
    (vl, vr) ← pure (g.get_estimate_verts a),
    if vl.visited ∧ vr.visited then
      find_most_interesting_aux_2 rest
    else do
      (best, others) ← find_most_interesting_aux_1 g fn a [] rest,
      return (best :: others)

meta def find_most_interesting (fn : improve_estimate_fn β) : tactic (global_state α β) := do
  new_interestings ← find_most_interesting_aux_2 g fn g.interesting_pairs,
  return ⟨ g.next_id, g.vertices, g.estimates, new_interestings, g.solving_edge, g.internal_strat_state ⟩ 

end global_state

meta def refresh_fn (α β : Type) : Type :=
  global_state α β → global_state α β

meta inductive strategy_action {α β : Type}
  | examine : dist_estimate β → side → strategy_action
  | refresh : refresh_fn α β → strategy_action
  | abort   : string → strategy_action
  
open strategy_action

meta def step_fn (α β : Type) : Type := global_state α β → ℕ → global_state α β × (@strategy_action α β)

meta structure strategy {α β : Type} :=
  (init : α)
  (step : step_fn α β)

  (init_bound : init_bound_fn β)
  (improve_estimate_over : improve_estimate_fn β)

structure config := 
  (trace      : bool := ff)
  (visualiser : bool := ff)

meta structure tracer (γ : Type) :=
  (init            : tactic γ)
  (publish_vertex  : γ → vertex → tactic unit)
  (publish_edge    : γ → edge → tactic unit)
  (publish_pair    : γ → vertex_ref → vertex_ref → tactic unit)
  (publish_finished: γ → tactic unit)
  (dump            : γ → string → tactic unit)
  (pause           : γ → tactic unit)

meta structure tracer_state (γ : Type) :=
  (tr       : tracer γ)
  (internal : γ)

meta def unit_tracer_init : tactic unit := return ()
meta def unit_tracer_publish_vertex (_ : unit) (_ : vertex) : tactic unit := tactic.skip
meta def unit_tracer_publish_edge (_ : unit) (_ : edge) : tactic unit := tactic.skip
meta def unit_tracer_publish_pair (_ : unit) (_ _ : vertex_ref) : tactic unit := tactic.skip
meta def unit_tracer_publish_finished (_ : unit) : tactic unit := tactic.skip
meta def unit_tracer_dump (_ : unit) (_ : string) : tactic unit := tactic.skip
meta def unit_tracer_pause (_ : unit) : tactic unit := tactic.skip
meta def unit_tracer : tracer unit :=
  ⟨ unit_tracer_init, unit_tracer_publish_vertex, unit_tracer_publish_edge, unit_tracer_publish_pair,
    unit_tracer_publish_finished, unit_tracer_dump, unit_tracer_pause ⟩

meta structure inst (α β γ : Type) :=
  (conf   : config)
  (rs     : list (expr × bool))
  (strat  : @strategy α β)
  (g      : global_state α β)
  (tr_state : tracer_state γ)

meta def inst.mutate {α β γ : Type} (i : inst α β γ) (g : global_state α β) : inst α β γ:=
  ⟨ i.conf, i.rs, i.strat, g, i.tr_state ⟩

meta def inst.trace {α β γ δ : Type} [has_to_tactic_format δ] (i : inst α β γ) (s : δ) : tactic unit :=
  if i.conf.trace then
    tactic.trace s
  else
    tactic.skip

meta def tracer_vertex_added {α β γ : Type} (i : inst α β γ) (v : vertex) : tactic unit := do
  --FIXME guard all of these with an if (to prevent pointless string building)
  i.trace format!"addV({v.id.to_string}): {v.pp}",
  i.tr_state.tr.publish_vertex i.tr_state.internal v

meta def tracer_edge_added {α β γ : Type} (i : inst α β γ) (e : edge) : tactic unit := do
  --FIXME guard all of these with an if (to prevent pointless string building)
  i.trace format!"addE: {e.f.to_string}→{e.t.to_string}",
  i.tr_state.tr.publish_edge i.tr_state.internal e

meta def tracer_pair_added {α β γ : Type} (i : inst α β γ) (l r : vertex_ref) : tactic unit := do
  --FIXME guard all of these with an if (to prevent pointless string building)
  i.trace format!"addP: {l.to_string}→{r.to_string}",
  i.tr_state.tr.publish_pair i.tr_state.internal l r

meta def tracer_dump {α β γ δ : Type} [has_to_tactic_format δ] (i : inst α β γ) (s : δ) : tactic unit := do
  --FIXME guard all of these with an if (to prevent pointless string building)
  fmt ← has_to_tactic_format.to_tactic_format s,
  str ← pure (to_string fmt),
  i.trace str,
  i.tr_state.tr.dump i.tr_state.internal str

meta def tracer_search_finished {α β γ : Type} (i : inst α β γ) : tactic unit := do
  --FIXME guard all of these with an if (to prevent pointless string building)
  i.trace format!"DONE!",
  i.tr_state.tr.publish_finished i.tr_state.internal

meta def dump_rws : list (expr × expr × ℕ × ℕ) → tactic unit
  | [] := tactic.skip
  | (a :: rest) := do tactic.trace format!"→{a.1}\nPF:{a.2}", dump_rws rest

meta def dump_vertices {α β γ : Type} (i : inst α β γ) : list vertex → tactic unit
  | [] := tactic.skip
  | (a :: rest) := do
    let pfx : string := match a.parent with
      | none := "?"
      | some p := p.f.to_string
    end,
    tracer_dump i (to_string format!"V{a.id.to_string}:{a.pp}<-{pfx}:{a.root}"),
    dump_vertices rest

meta def dump_edges {α β γ : Type} (i : inst α β γ) : list edge → tactic unit
  | [] := tactic.skip
  | (a :: rest) := do
    let (vf, vt) := i.g.get_endpoints a,
    tracer_dump i "E:{vf.pp}→{vt.pp}",
    dump_edges rest

meta def dump_estimates {α β γ : Type} (i : inst α β γ) : list (dist_estimate β) → tactic unit
  | [] := tactic.trace ""
  | (a :: rest) := do
  tracer_dump i format!"I{(i.g.get_vertex a.l).pp}-{(i.g.get_vertex a.r).pp}:{a.bnd.bound}",
  dump_estimates rest

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def inst.do_add_vertex {α β γ : Type} (i : inst α β γ) (e : expr) (root : bool) (s : option side)
  : tactic (inst α β γ × vertex) := do
  maybe_v ← i.g.find_vertex e,
  match maybe_v with
    | none := do
      (g, v) ← i.g.do_alloc_vertex e root s,
      tracer_vertex_added i v,
      return (i.mutate g, v)
    | (some v) := return (i, v)
  end

meta def inst.add_vertex {α β γ : Type} (i : inst α β γ) (e : expr) (s : option side) :=
  i.do_add_vertex e ff s

meta def inst.add_root_vertex {α β γ : Type} (i : inst α β γ) (e : expr) (s : side) :=
  i.do_add_vertex e tt s

meta def inst.add_edge {α β γ : Type} (i : inst α β γ) (f t : vertex)
  (proof : expr) (how : ℕ) : tactic (inst α β γ × edge) := do
  let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
  tracer_edge_added i new_edge,
  g ← pure i.g,
  (g, f) ← g.add_adj f new_edge,
  (g, t) ← g.add_adj t new_edge,
  (g, t) ← g.publish_parent f t new_edge,
  if ¬(vertex.same_side f t) then
    return (i.mutate (g.register_solved new_edge), new_edge)
  else
    return (i.mutate g, new_edge)

-- Add an "interesting pair" to the global state
meta def inst.add_pair {α β γ : Type} (i : inst α β γ) (l r : vertex) : tactic (inst α β γ) := do
  tracer_pair_added i l.id r.id,
  match i.g.find_pair l.id r.id with
    | some de := return i
    | none := do
        g ← i.g.do_alloc_pair ⟨ l.id, r.id, i.strat.init_bound l r ⟩,
        return (i.mutate g)
    end

meta def inst.find_most_interesting {α β γ : Type} (i : inst α β γ) : tactic (inst α β γ) := do
  g ← i.g.find_most_interesting i.strat.improve_estimate_over,
  return (i.mutate g)

meta def store_new_equalities {α β γ : Type} (f : vertex) : inst α β γ → list (expr × expr × ℕ × ℕ) → tactic (inst α β γ × list vertex × list edge)
  | i [] := return (i, [], [])
  | i ((new_expr, prf, id, j) :: rest) := do
      (i, v) ← i.add_vertex new_expr f.s,
      (i, e) ← i.add_edge f v prf id,
      (i, vs, es) ← store_new_equalities i rest,
      return (i, (v :: vs), (e :: es))

meta def add_new_interestings {α β γ : Type} (v : vertex) : inst α β γ → list vertex → tactic (inst α β γ)
  | i [] := return i
  | i (a :: rest) := do
      i ← i.add_pair v a,
      add_new_interestings i rest

-- My job is to examine the specified side and to blow up the vertex once
meta def inst.examine_one {α β γ : Type} (i : inst α β γ) (de : dist_estimate β) (s : side) : tactic (inst α β γ) := do
  let v := i.g.get_vertex (de.side s),
  -- let flip := match s with
  --   | side.L := ff
  --   | side.R := tt
  -- end,
  all_rws ← all_rewrites_list i.rs ff v.exp,
  (i, touched_verts, new_edges) ← store_new_equalities v i all_rws,
  i ← pure (i.mutate (i.g.mark_vertex_visited v.id)),
  --FIXME this next line could use some improving
  --we might also want to mark all of the immediate children of "(i.g.get_vertex (de.side s.other))" as interesting
  i ← add_new_interestings (i.g.get_vertex (de.side s.other)) i touched_verts,
  i ← i.find_most_interesting,
  return i

meta def inst.step_once {α β γ : Type} (i : inst α β γ) (itr : ℕ) : tactic (inst α β γ × status) :=
  match i.g.solving_edge with
  | some e := return (i, status.done e)
  | none :=
    let (g, action) := i.strat.step i.g itr in
    let i := i.mutate g in
    match action with
      | examine de s := do
        target ← pure (g.get_vertex (de.side s)),
        buddy ← pure (g.get_vertex (de.side s.other)),
        i.trace format!"examine ({target.pp})↔({buddy.pp})",
        if target.visited then do
          i.trace format!"abort: already visited vertex!",
          return (i, status.abort)
        else do
          i ← i.examine_one de s,
          return (i, status.going (itr + 1))
      | refresh ref_fn := do
        i.trace format!"refresh",
        return (i.mutate (ref_fn i.g), status.going (itr + 1))
      | abort reason := do
        i.trace format!"abort: {reason}",
        return (i, status.abort)
    end
  end

meta def inst.backtrack_to_root_with {α β γ : Type} (i : inst α β γ) : vertex → expr → tactic expr :=
  λ (cur : vertex) (prf_so_far : expr), do
  match cur.parent with
    | none := return prf_so_far
    | some e := do
      let parent : vertex := i.g.get_vertex e.f,
      new_expr ← tactic.mk_eq_trans e.proof prf_so_far,
      inst.backtrack_to_root_with parent new_expr
  end

--FIXME code duplication with above
meta def inst.backtrack_to_root {α β γ : Type} (i : inst α β γ) (cur : vertex) : tactic (option expr) := do
  match cur.parent with
    | none := return none
    | some e := do
      let parent : vertex := i.g.get_vertex e.f,
      proof ← i.backtrack_to_root_with parent e.proof,
      return proof
  end

meta def flip_half (h : expr) : tactic expr := tactic.mk_eq_symm h
meta def unify_halves (l r : expr) : tactic expr := tactic.mk_eq_trans l r

meta def inst.solve_goal {α β γ : Type} (i : inst α β γ) (e : edge) : tactic string := do
  let (vf, vt) := i.g.get_endpoints e,

  rhs_half ← i.backtrack_to_root_with vf e.proof,
  rhs_half ← flip_half rhs_half,

  lhs_half ← i.backtrack_to_root vt,
  match lhs_half with
    | some lhs_half := do
      proof ← unify_halves lhs_half rhs_half,
      proof ← match vf.s with
        | some side.L := flip_half proof
        | _           := pure proof
      end,

      pp ← pretty_print proof,
      i.trace pp,
      i.trace vf.to_string,
      i.trace vt.to_string,

      tactic.exact proof
    | none := tactic.skip
  end,

  return "pretty version"

meta def inst.search_until_stop_aux {α β γ : Type} : inst α β γ → ℕ → tactic search_result := λ i itr, do
  (i, s) ← i.step_once itr,
  match s with
    | status.going k := inst.search_until_stop_aux i (itr + 1)
    | status.abort   := return (search_result.failure "aborted")
    | status.done e  := do
      str ← i.solve_goal e,
      return (search_result.success str)
  end

meta def inst.search_until_abort {α β γ : Type} (i : inst α β γ) : tactic search_result := do
  res ← i.search_until_stop_aux 0,
  tracer_search_finished i,
  return res

meta def mk_initial_global_state {α β : Type} (strat : @strategy α β) : global_state α β :=
  ⟨ mk_vertex_ref_first, [], [], [], none, strat.init ⟩

meta def mk_initial_tracer_state {γ : Type} (tr : tracer γ) : tactic (tracer_state γ) := do
  internal ← tr.init,
  return ⟨ tr, internal ⟩

meta def mk_search_instance {α β γ : Type} (conf : config) (rs : list (expr × bool)) (strat : @strategy α β) (lhs rhs : expr) (tr : tracer γ)
  : tactic (inst α β γ) := do
  tracer_state ← mk_initial_tracer_state tr,
  let i := inst.mk conf rs strat (mk_initial_global_state strat) tracer_state,
  (i, vl) ← i.add_root_vertex lhs side.L,
  (i, vr) ← i.add_root_vertex rhs side.R,
  i ← i.add_pair vl vr,
  return i

end tidy.rewrite_search