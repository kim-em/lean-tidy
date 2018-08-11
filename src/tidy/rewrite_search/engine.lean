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
inductive bound_progress {β : Type}
  | exactly : ℕ → bound_progress
  | at_least : ℕ → β → bound_progress
open bound_progress
def bound_progress.bound {β : Type} : @bound_progress β → ℕ
  | (exactly n)    := n
  | (at_least n _) := n
def bound_progress.sure {β : Type} : @bound_progress β → bool
  | (exactly _)    := tt
  | (at_least _ _) := ff
def bound_progress.to_string {β : Type} : @bound_progress β → string
  | (exactly n)    := "=" ++ to_string n
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
  (how   : ℕ)

meta structure vertex :=
  (id      : vertex_ref)
  (exp     : expr)
  (pp      : string)
  (tokens  : list string)

  (root    : bool)
  (visited : bool)
  (s       : option side)
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
  (bnd : @bound_progress state_type)
def dist_estimate.side {α : Type} (de : dist_estimate α) (s : side) : vertex_ref :=
  match s with
  | side.L := de.l
  | side.R := de.r
  end
def dist_estimate.to_string {α : Type} (de : dist_estimate α) : string :=
  (de.l.to_string) ++ "-" ++ (de.r.to_string) ++ "Δ" ++ de.bnd.to_string

meta def init_bound_fn (β : Type) := vertex → vertex → @bound_progress β
meta def improve_estimate_fn (β : Type) := ℕ → vertex → vertex → @bound_progress β → @bound_progress β

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

-- Retrieve the vertex with the given ref, or the null vertex if it is not
-- present.
meta def global_state.get_vertex {α β : Type} (g : global_state α β) (r : vertex_ref) : vertex :=
  list_at mk_null_vertex g.vertices r

meta def global_state.set_vertex {α β : Type} (g : global_state α β) (v : vertex) : (global_state α β) :=
  ⟨ g.next_id, list_set_at g.vertices v.id v, g.estimates, g.interesting_pairs, g.solving_edge, g.internal_strat_state ⟩

meta def global_state.get_endpoints {α β : Type} (g : global_state α β) (e : edge) : vertex × vertex :=
  (g.get_vertex e.f, g.get_vertex e.t)

meta def global_state.get_estimate_verts {α β : Type} (g : global_state α β) (de : dist_estimate β) : vertex × vertex :=
  (g.get_vertex de.l, g.get_vertex de.r)

meta def dump_rws : list (expr × expr × ℕ × ℕ) → tactic unit
  | [] := tactic.trace ""
  | (a :: rest) := do tactic.trace format!"→{a.1}\nPF:{a.2}", dump_rws rest

meta def dump_vertices : list vertex → tactic unit
  | [] := tactic.trace ""
  | (a :: rest) := do
    let pfx : string := match a.parent with
      | none := "?"
      | some p := p.f.to_string
    end,
    tactic.trace format!"V{a.id.to_string}:{a.pp}<-{pfx}",
    dump_vertices rest

meta def dump_estimates {α β : Type} (g : global_state α β) : list (dist_estimate β) → tactic unit
  | [] := tactic.trace ""
  | (a :: rest) := do
  tactic.trace format!"I{(g.get_vertex a.l).pp}-{(g.get_vertex a.r).pp}:{a.bnd.bound}",
  dump_estimates rest
  
-- Forcibly add a new vertex to the vertex table. Probably should never be 
-- called by a strategy and add_vertex to should used instead.
meta def global_state.do_alloc_vertex {α β : Type} (g : global_state α β) (e : expr) (root : bool) (s : option side)
  : tactic (global_state α β × vertex) := do
  (pp, tokens) ← tokenise_expr e,
  let v : vertex := ⟨ g.next_id, e, pp, tokens, root, ff, s, none, [] ⟩,
  return (⟨ g.next_id.next, g.vertices.append [v], g.estimates, g.interesting_pairs, g.solving_edge,g.internal_strat_state ⟩, v)
  
-- Forcibly add a new pair to the interesting pair list. Probably should never be 
-- called by a strategy and add_vertex to should used instead.
meta def global_state.do_alloc_pair {α β : Type} (g : global_state α β) (de : dist_estimate β)
  : tactic (global_state α β) := do
  return (⟨ g.next_id, g.vertices, g.estimates.append [de], g.interesting_pairs.append [de], g.solving_edge, g.internal_strat_state ⟩)

meta def global_state_find_vertex_aux (pp : string) : list vertex → option vertex
| [] := none
| (a :: rest) := if a.pp = pp then some a else global_state_find_vertex_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def global_state.find_vertex {α β : Type} (g : global_state α β) (e : expr) : tactic (option vertex) := do
  pp ← pretty_print e,
  return (global_state_find_vertex_aux pp g.vertices)

meta def global_state_find_pair_aux {β : Type} (l r : vertex_ref) : list (dist_estimate β) → option (dist_estimate β)
| [] := none
| (a :: rest) :=
  if (a.l = l ∧ a.r = r) ∨ (a.l = r ∧ a.r = l) then
    some a
  else
    global_state_find_pair_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def global_state.find_pair {α β : Type} (g : global_state α β) (l r : vertex_ref) : option (dist_estimate β) :=
  global_state_find_pair_aux l r g.estimates

meta def global_state.register_solved {α β : Type} (g : global_state α β) (e : edge) : global_state α β :=
  ⟨ g.next_id, g.vertices, g.estimates, g.interesting_pairs, some e, g.internal_strat_state ⟩

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def global_state.do_add_vertex {α β : Type} (g : global_state α β) (e : expr) (root : bool) (s : option side)
  : tactic (global_state α β × vertex) := do
  maybe_v ← g.find_vertex e,
  match maybe_v with
    | none := do
      (g, v) ← g.do_alloc_vertex e root s,
      -- tactic.trace format!"addV: {v.pp}",
      return (g, v)
    | (some v) := return (g, v)
  end

meta def global_state.add_vertex {α β : Type} (g : global_state α β) (e : expr) :=
  global_state.do_add_vertex g e ff none

meta def global_state.add_root_vertex {α β : Type} (g : global_state α β) (e : expr) (s : side) :=
  global_state.do_add_vertex g e tt s

meta def global_state.add_adj {α β : Type} (g : global_state α β) (v : vertex)
  (e : edge) : tactic (global_state α β × vertex) := do
  let v : vertex := ⟨ v.id, v.exp, v.pp, v.tokens, v.visited, v.root, v.s, v.parent, v.adj.append [e] ⟩,
  return (g.set_vertex v, v)

meta def global_state.publish_parent {α β : Type} (f t : vertex) (g : global_state α β)
  (e : edge) : tactic (global_state α β × vertex) :=
  if t.root then
    return (g, t)
  else
  match t.parent with
    | some parent := return (g, t)
    | none := do
      let t : vertex := ⟨ t.id, t.exp, t.pp, t.tokens, t.root, t.visited, f.s, some e, t.adj ⟩,
      return (g.set_vertex t, t)
  end

meta def global_state.mark_vertex_visited {α β : Type} (g : global_state α β) (vr : vertex_ref)
  : global_state α β :=
  let v := g.get_vertex vr in
  g.set_vertex ⟨ v.id, v.exp, v.pp, v.tokens, v.root, tt, v.s, v.parent, v.adj ⟩

meta def global_state.add_edge {α β : Type} (g : global_state α β) (f t : vertex)
  (proof : expr) (how : ℕ) : tactic (global_state α β × edge) := do
  let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
  -- tactic.trace format!"addE:{f.to_string}→{t.to_string}",
  (g, f) ← g.add_adj f new_edge,
  (g, t) ← g.add_adj t new_edge,
  (g, t) ← g.publish_parent f t new_edge,
  if ¬(vertex.same_side f t) then
    return (g.register_solved new_edge, new_edge)
  else
    return (g, new_edge)

-- updates rival's estimate trying to beat candidate's estimate, stopping if we do or we can't
-- go any further. We return true if we were able to beat candidate.
meta def try_to_beat {β : Type} (fn : @improve_estimate_fn β) (candidate rival : @bound_progress β)
  (rival_l rival_r : vertex) : @bound_progress β × bool :=
  let m := candidate.bound in
  match rival with
  | exactly n := (rival, n <= m)
  | at_least n p :=
    let attempt := fn m rival_l rival_r rival in
    (attempt, attempt.bound < m)
  end

-- First is closer
meta def sort_most_interesting {α β : Type} (g : global_state α β) (fn : @improve_estimate_fn β)
  : dist_estimate β → dist_estimate β → tactic (dist_estimate β × dist_estimate β)
  | a b := do
  match try_to_beat fn a.bnd b.bnd (g.get_vertex b.l) (g.get_vertex b.r) with
    -- b is guarenteed closer, so return it:
    | (new_b, ff) := return (⟨ b.l, b.r, new_b ⟩, a)
    -- otherwise:
    | (new_b, tt) := match a.bnd with
      -- b is further than the current estimate for a and the estimate for a is exact:
      | exactly k    := return (a, ⟨ b.l, b.r, new_b ⟩)
      -- or, b is futher than the current estimate for a but a might actually be worse, so check:
      | at_least k p := sort_most_interesting ⟨ b.l, b.r, new_b ⟩ a
    end
  end

meta def find_most_interesting_aux {α β : Type} (g : global_state α β) (fn : @improve_estimate_fn β)
  : dist_estimate β → list (dist_estimate β) → list (dist_estimate β) → tactic (dist_estimate β × list (dist_estimate β))
  | current_best seen [] := return (current_best, seen)
  | current_best seen (a :: rest) := do
    (vl, vr) ← pure (g.get_estimate_verts a),
    -- Drop "interesting" vertices which have had both ends visited, and hence aren't interesting
    -- any more.
    if vl.visited ∧ vr.visited then
      find_most_interesting_aux current_best seen rest
    else do
      (better, worse) ← sort_most_interesting g fn current_best a,
      r ← find_most_interesting_aux better (worse :: seen) rest,
      return r

meta def find_most_interesting {α β : Type} (g : global_state α β) (fn : @improve_estimate_fn β)
  : list (dist_estimate β) → tactic (list (dist_estimate β))
  | [] := return []
  | (a :: rest) := do
    (vl, vr) ← pure (g.get_estimate_verts a),
    if vl.visited ∧ vr.visited then
      find_most_interesting rest
    else do
      (best, others) ← find_most_interesting_aux g fn a [] rest,
      return (best :: others)

meta def global_state.find_most_interesting {α β : Type} (g : global_state α β) (fn : @improve_estimate_fn β) : tactic (global_state α β) := do
  -- dump_estimates g g.interesting_pairs,
  new_interestings ← find_most_interesting g fn g.interesting_pairs,
  return ⟨ g.next_id, g.vertices, g.estimates, new_interestings, g.solving_edge, g.internal_strat_state ⟩ 

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
  (trace : bool := ff)

meta structure inst (α β : Type) :=
  (conf  : config)
  (rs    : list (expr × bool))
  (strat : @strategy α β)
  (g     : global_state α β)

meta def inst.mutate {α β : Type} (i : inst α β) (g : global_state α β) : inst α β :=
  ⟨ i.conf, i.rs, i.strat, g ⟩

-- Add an "interesting pair" to the global state
meta def inst.add_pair {α β : Type} (i : inst α β) (l r : vertex) : tactic (inst α β) := do
  -- tactic.trace format!"add_pair:({l.pp}, {r.pp})",
  match i.g.find_pair l.id r.id with
    | some de := return i
    | none := do
        g ← i.g.do_alloc_pair ⟨ l.id, r.id, i.strat.init_bound l r ⟩,
        return (i.mutate g)
    end

meta def inst.find_most_interesting {α β : Type} (i : inst α β) : tactic (inst α β) := do
  g ← i.g.find_most_interesting i.strat.improve_estimate_over,
  return (i.mutate g)

meta def store_new_equalities {α β : Type} (f : vertex) : global_state α β → list (expr × expr × ℕ × ℕ) → tactic (global_state α β × list vertex × list edge)
  | g [] := return (g, [], [])
  | g ((new_expr, prf, i, j) :: rest) := do
      (g, v) ← g.add_vertex new_expr,
      (g, e) ← g.add_edge f v prf i,
      (g, vs, es) ← store_new_equalities g rest,
      return (g, (v :: vs), (e :: es))

meta def add_new_interestings {α β : Type} (v : vertex) : inst α β → list vertex → tactic (inst α β)
  | i [] := return i
  | i (a :: rest) := do
      i ← i.add_pair v a,
      add_new_interestings i rest

-- My job is to examine the specified side and to blow up the vertex once
meta def inst.examine_one {α β : Type} (i : inst α β) (de : dist_estimate β) (s : side) : tactic (inst α β) := do
  let v := i.g.get_vertex (de.side s),
  all_rws ← all_rewrites_list i.rs v.exp,
  (g, touched_verts, new_edges) ← store_new_equalities v i.g all_rws,
  g ← pure (g.mark_vertex_visited v.id),
  i ← pure (i.mutate g),
  i ← add_new_interestings (i.g.get_vertex (de.side s.other)) i touched_verts,
  i ← i.find_most_interesting,
  return i

meta def inst.step_once {α β : Type} (i : inst α β) (itr : ℕ) : tactic (inst α β × status) :=
  match i.g.solving_edge with
  | some e := return (i, status.done e)
  | none :=
    let (g, action) := i.strat.step i.g itr in
    let i := i.mutate g in
    match action with
      | examine de s := do
        target ← pure (g.get_vertex (de.side s)),
        buddy ← pure (g.get_vertex (de.side s.other)),
        tactic.trace format!"examine {target.pp}-{buddy.pp}",
        -- dump_vertices g.vertices,
        -- dump_estimates g g.interesting_pairs,
        if target.visited then do
          tactic.trace format!"abort: already visited vertex!",
          return (i, status.abort)
        else do
          i ← i.examine_one de s,
          return (i, status.going (itr + 1))
      | refresh ref_fn := do
        tactic.trace format!"refresh",
        return (i.mutate (ref_fn i.g), status.going (itr + 1))
      | abort reason := do
        tactic.trace format!"abort: {reason}",
        return (i, status.abort)
    end
  end

meta def inst.backtrack_to_root_with {α β : Type} (i : inst α β) : vertex → expr → tactic expr :=
  λ (cur : vertex) (prf_so_far : expr), do
  match cur.parent with
    | none := return prf_so_far
    | some e := do
      let parent : vertex := i.g.get_vertex e.f,
      new_expr ← tactic.mk_eq_trans e.proof prf_so_far,
      inst.backtrack_to_root_with parent new_expr
  end

--FIXME code duplication with above
meta def inst.backtrack_to_root {α β : Type} (i : inst α β) (cur : vertex) : tactic (option expr) := do
  match cur.parent with
    | none := return none
    | some e := do
      let parent : vertex := i.g.get_vertex e.f,
      proof ← i.backtrack_to_root_with parent e.proof,
      return proof
  end

meta def flip_half (h : expr) : tactic expr := tactic.mk_eq_symm h
meta def unify_halves (l r : expr) : tactic expr := tactic.mk_eq_trans l r

meta def inst.solve_goal {α β : Type} (i : inst α β) (e : edge) : tactic string := do
  let (vf, vt) := i.g.get_endpoints e,
  
  rhs_half ← i.backtrack_to_root_with vf e.proof,
  rhs_half ← flip_half rhs_half,

  lhs_half ← i.backtrack_to_root vt,
  match lhs_half with
    | some lhs_half := do
      proof ← unify_halves lhs_half rhs_half,
      proof ← match vf.s with
        | some side.L := tactic.mk_eq_symm proof
        | _           := pure proof
      end,

      pp ← pretty_print proof,
      tactic.trace pp,
      tactic.trace vf.to_string,
      tactic.trace vt.to_string,

      tactic.exact proof
    | none := tactic.skip
  end,

  return "aaaaaa pretty version"

meta def inst.search_until_stop_aux {α β : Type} : inst α β → ℕ → tactic search_result := λ i itr, do
  (i, s) ← i.step_once itr,
  match s with
    | status.going k := inst.search_until_stop_aux i (itr + 1)
    | status.abort   := return (search_result.failure "aborted")
    | status.done e  := do
      str ← i.solve_goal e,
      return (search_result.success str)
  end

meta def inst.search_until_abort {α β : Type} (i : inst α β) : tactic search_result :=
  i.search_until_stop_aux 0

meta def mk_initial_global_state {α β : Type} (strat : @strategy α β) : global_state α β :=
  ⟨ mk_vertex_ref_first, [], [], [], none, strat.init ⟩

meta def mk_search_instance {α β : Type} (conf : config) (rs : list (expr × bool)) (strat : @strategy α β) (lhs rhs : expr)
  : tactic (inst α β) := do
  let g := mk_initial_global_state strat,
  (g, vl) ← g.add_root_vertex lhs side.L,
  (g, vr) ← g.add_root_vertex rhs side.R,
  let i := inst.mk conf rs strat g,
  i ← i.add_pair vl vr,
  return i

end tidy.rewrite_search