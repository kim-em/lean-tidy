import tidy.rewrite_search.core

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.strategy.pexplore

structure pexplore_config :=
(pop_size      : ℕ := 100)
(pop_alternate : bool := ff)
-- TODO consider putting something like this back, with an "alternate" flag or similar
-- (list_combinator : list pair → list pair → list pair := list.multiplex /-c.f. list.append-/)

structure pair_stream :=
(last_side : side)
(its : sided_pair rewriterator)

inductive ipair
| unresolved (p : pair) (de : table_ref) : ipair
| resolved (p : pair) (de : table_ref) (ps : pair_stream) : ipair
def ipair.pair : ipair → pair
| (ipair.unresolved p de) := p
| (ipair.resolved p de _) := p
def ipair.de : ipair → table_ref
| (ipair.unresolved p de) := de
| (ipair.resolved p de _) := de
def ipair.to_string : ipair → string
| (ipair.unresolved p de) := to_string p ++ "@" ++ to_string de ++ "?"
| (ipair.resolved p de _) := to_string p ++ "@" ++ to_string de ++ "!"
instance has_to_string : has_to_string ipair := ⟨ipair.to_string⟩

structure pexplore_state :=
(interesting_pairs : list ipair)

variables {β γ δ : Type} (conf : pexplore_config) (m : metric pexplore_state β γ δ) (g : search_state pexplore_state β γ δ)

namespace pair_stream

meta def from_vertices (vl vr : vertex) : tactic (search_state pexplore_state β γ δ × pair_stream) := do
  (g, lhs_it) ← g.visit_vertex vl,
  (g, rhs_it) ← g.visit_vertex vr,
  return (g, ⟨side.L, ⟨lhs_it, rhs_it⟩⟩)

meta def from_estimate (de : dist_estimate γ) : tactic (search_state pexplore_state β γ δ × pair_stream) := do
  (vl, vr) ← g.get_estimate_verts de,
  from_vertices g vl vr

meta instance : has_to_format $ option pair := ⟨λ op, match op with | none := "none" | some p := to_string p end⟩
meta instance aa : has_to_format pair := ⟨λ p, to_string p⟩

meta def read_side (ps : pair_stream) (g : search_state pexplore_state β γ δ) (p : pair) (s : side) : tactic (search_state pexplore_state β γ δ × pair_stream × option pair) := do
  (g, it, nxt) ← (ps.its.get s).next g,
  let newp : option pair := match nxt with
  | some (v, e) := some ⟨p.get s.other, v.id⟩
  | none := none
  end,
  (vl, vr) ← g.lookup_pair p,
  return (g, {ps with last_side := s, its := ps.its.set s it}, newp)

meta def read (ps : pair_stream) (g : search_state pexplore_state β γ δ) (conf : pexplore_config) (p : pair) : tactic (search_state pexplore_state β γ δ × pair_stream × option pair) := do
  let next_side := if conf.pop_alternate then ps.last_side.other else ps.last_side,
  (g, ps, ret) ← ps.read_side g p next_side,
  match ret with
  | some _ := return (g, ps, ret)
  | none := ps.read_side g p next_side.other
  end

end pair_stream

-- updates rival's estimate tryg to beat candidate's estimate, stoppg if we do or we can't
-- go any further. We return true if we were able to beat candidate.
private meta def try_to_beat (candidate rival : dist_estimate γ) : tactic (search_state pexplore_state β γ δ × dist_estimate γ × bool) :=
let cbnd := candidate.bnd.bound in
match rival.bnd with
| exactly n _ := return (g, rival, n <= cbnd)
| at_least n p := do
  (g, attempt) ← g.improve_estimate_over m cbnd rival,
  return (g, attempt, attempt.bnd.bound < cbnd)
end

-- First is closer
private meta def sort_most_interesting : search_state pexplore_state β γ δ → ipair × dist_estimate γ → ipair × dist_estimate γ → tactic (search_state pexplore_state β γ δ × (ipair × dist_estimate γ) × (ipair × dist_estimate γ))
| g (a, a_de) (b, b_de) := do
  (g, new_b_de, better) ← try_to_beat m g a_de b_de,
  match better with
  -- b is guarenteed closer, so return it:
  | tt := return (g, (b, new_b_de), (a, a_de))
  -- otherwise:
  | ff := match a_de.bnd with
    -- b is further than the current estimate for a and the estimate for a is exact:
    | exactly k _ := return (g, (a, a_de), (b, new_b_de))
    -- or, b is futher than the current estimate for a but a might actually be worse, so check:
    | at_least k p := sort_most_interesting g (b, new_b_de) (a, a_de)
  end
end

private meta def find_most_interesting_aux : search_state pexplore_state β γ δ → ipair × dist_estimate γ → list ipair → list ipair → tactic (search_state pexplore_state β γ δ × ipair × list ipair)
| g (curr_best, curr_de) seen [] := return (g, curr_best, seen)
| g (curr_best, curr_de) seen (candidate :: rest) := do
  candidate_de ← g.estimates.get candidate.de,
  (g, (better, better_de), (worse, worse_de)) ← sort_most_interesting m g (curr_best, curr_de) (candidate, candidate_de),
  find_most_interesting_aux g (better, better_de) (worse :: seen) rest

meta def find_most_interesting : tactic (search_state pexplore_state β γ δ × option ipair × list ipair) :=
  match g.strat_state.interesting_pairs with
  | []          := return (g, none, [])
  | (a :: rest) := do
    a_de ← g.estimates.get a.de,
    (g, best, others) ← find_most_interesting_aux m g (a, a_de) [] rest,
    return (g, some best, others)
  end

meta def resolve_ipair : ipair → tactic (search_state pexplore_state β γ δ × ipair)
| (ipair.unresolved p ref) := do
  de ← g.estimates.get ref,
  (g, _) ← g.try_unify de.to_pair,
  (g, ps) ← pair_stream.from_estimate g de,
  return (g, ipair.resolved p ref ps)
| ip := return (g, ip)

meta def pop_ipairs_aux : search_state pexplore_state β γ δ → metric pexplore_state β γ δ → ℕ → ipair → tactic (search_state pexplore_state β γ δ × ipair × list ipair)
| g m        0 ip := return (g, ip, [])
| g m pop_size (ipair.unresolved p ref) := do
  (g, ip) ← resolve_ipair g (ipair.unresolved p ref),
  pop_ipairs_aux g m pop_size ip
| g m pop_size (ipair.resolved p ref ps) := do
  (g, ps, nxt) ← ps.read g conf p,
  let ip := ipair.resolved p ref ps,
  match nxt with
  | none := return (g, ip, [])
  | some nxt := do
    match g.estimates.find (λ de, nxt = de.to_pair ∨ (nxt = de.to_pair.flip)) with
    | none := do
      (g, ref) ← g.alloc_estimate m nxt,
      let newip := ipair.unresolved nxt ref,
      (g, ip, others) ← pop_ipairs_aux g m (pop_size - 1) ip,
      return (g, ipair.resolved p ref ps, list.cons newip others)
    | some de := pop_ipairs_aux g m pop_size ip
    end
  end

meta def pop_ipairs (pop_size : ℕ) (ip : ipair) : tactic (search_state pexplore_state β γ δ × ipair × list ipair) := do
  (g, ip, new) ← pop_ipairs_aux conf g m pop_size ip,
  return (g, ip, new)

meta def pexplore_init : pexplore_state := ⟨ [] ⟩

meta def pexplore_startup (m : metric pexplore_state β γ δ) (l r : vertex) : tactic (search_state pexplore_state β γ δ) := do
  let p : pair := ⟨l.id, r.id⟩,
  (g, ref) ← g.alloc_estimate m p,
  return $ g.mutate_strat ⟨ [ipair.unresolved p ref] ⟩

meta def pexplore_step : search_state pexplore_state β γ δ → metric pexplore_state β γ δ → ℕ → tactic (search_state pexplore_state β γ δ × status)
| g m itr := do
  tactic.trace format!"#{g.strat_state.interesting_pairs.length}",
  (g, best, others) ← find_most_interesting m g,
  match (best, others) with
  | (none, []) := return (g, status.abort "all interesting pairs exhausted!")
  | (none, _) := pexplore_step g m itr
  | (some best, others) := do
    (g, best, new) ← pop_ipairs conf m g conf.pop_size best,
    (new_head, s) ← pure $ match new with
    | [] := ([], status.repeat)
    | l  := (l.concat best, status.continue)
    end,
    return (g.mutate_strat {g.strat_state with interesting_pairs := new_head.append others }, s)
  end

end tidy.rewrite_search.strategy.pexplore

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.strategy.pexplore

meta def pexplore (conf : pexplore_config := {}) : strategy_constructor pexplore_state :=
λ β γ δ, strategy.mk pexplore_init (@pexplore_startup β γ δ) (@pexplore_step β γ δ conf)

end tidy.rewrite_search.strategy