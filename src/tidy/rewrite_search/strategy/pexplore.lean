import tidy.rewrite_search.engine

open tidy.rewrite_search
open tidy.rewrite_search.bound_progress

namespace tidy.rewrite_search.strategy.pexplore

structure pexplore_config :=
(pop_amt         : ℕ := 100)
(list_combinator : list pair → list pair → list pair := list.multiplex /-c.f. list.append-/)

inductive ipair
| unresolved (de : table_ref)                      : ipair
| resolved (de : table_ref) (children : list pair) : ipair
def ipair.de : ipair → table_ref
| (ipair.unresolved de) := de
| (ipair.resolved de _) := de

structure pexplore_state :=
(interesting_pairs : list ipair)

variables {β γ δ : Type} (conf : pexplore_config) (m : metric pexplore_state β γ δ) (g : search_state pexplore_state β γ δ)

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

meta def find_pairs (v rel_to : vertex) : tactic (search_state pexplore_state β γ δ × list pair) := do
  (g, adjs) ← g.visit_vertex v,
  return (g, adjs.map (λ u, ⟨u.id, rel_to.id⟩))

meta def resolve_ipair : ipair → tactic (search_state pexplore_state β γ δ × ipair × list pair)
| (ipair.resolved ref children) := return (g, ipair.resolved ref children, children)
| (ipair.unresolved ref) := do
  de ← g.estimates.get ref,
  (vl, vr) ← g.get_estimate_verts de,
  (g, lhs_pairs) ← find_pairs g vl vr,
  (g, rhs_pairs) ← find_pairs g vr vl,
  let all_pairs := conf.list_combinator lhs_pairs rhs_pairs,
  return (g, ipair.resolved ref all_pairs, all_pairs)

meta def pop_ipairs_aux : search_state pexplore_state β γ δ → metric pexplore_state β γ δ → ℕ → ipair → list pair → tactic (search_state pexplore_state β γ δ × ipair × list ipair)
| g m n ip [] := return (g, ip, [])
| g m n ip (a :: rest) := do
  match g.estimates.find a with
  | none := do
    (g, ref) ← g.alloc_estimate m a,
    let newip := ipair.unresolved ref,
    (g, ip, others) ← pop_ipairs_aux g m (n - 1) (ipair.resolved ip.de rest) rest,
    return (g, ipair.resolved ip.de rest, (newip :: others))
  | some de := pop_ipairs_aux g m n (ipair.resolved ip.de rest) rest
  end

meta def pop_ipairs (n : ℕ) (ip : ipair) : tactic (search_state pexplore_state β γ δ × ipair × list ipair) := do
  (g, ip, children) ← resolve_ipair conf g ip,
  pop_ipairs_aux g m n ip children

meta def pexplore_init : pexplore_state := ⟨ [] ⟩

meta def pexplore_startup (m : metric pexplore_state β γ δ) (l r : vertex) : tactic (search_state pexplore_state β γ δ) := do
  (g, ref) ← g.alloc_estimate m ⟨l.id, r.id⟩,
  return $ g.mutate_strat ⟨ [ipair.unresolved ref] ⟩

--FIXME prevent the same estimate pair but flipped from being considered if the original already is in the ipair list

meta def pexplore_step : search_state pexplore_state β γ δ → metric pexplore_state β γ δ → ℕ → tactic (search_state pexplore_state β γ δ × status)
| g m itr := do
  (g, best, others) ← find_most_interesting m g,
  match (best, others) with
  | (none, []) := return (g, status.abort "all interesting pairs exhausted!")
  | (none, _) := pexplore_step g m itr
  | (some best, others) := do
    (g, best, new) ← pop_ipairs conf m g conf.pop_amt best,
    (new_head, s) ← pure $ match new with
    | [] := ([], status.repeat)
    | l  := (l.concat best, status.continue)
    end,
    return (g.mutate_strat {g.strat_state with interesting_pairs := new_head.append others }, s)
  end

end tidy.rewrite_search.strategy.pexplore

namespace tidy.rewrite_search.strategy

open tidy.rewrite_search.strategy.pexplore

meta def pexplore (conf : pexplore_config := {}) : strategy_constructor pexplore_state := λ β γ δ, strategy.mk pexplore_init (@pexplore_startup β γ δ) (@pexplore_step β γ δ conf)

end tidy.rewrite_search.strategy