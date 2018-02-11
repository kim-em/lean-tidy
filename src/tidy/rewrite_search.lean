import data.list

open lean
open lean.parser

universes u

structure untraversed_vertex_data (α : Type u) :=
(label : α)
(parent : ℕ)
(depth : ℕ)

structure traversed_vertex_data (α : Type u) extends untraversed_vertex_data α :=
(traversed_neighbours : list ℕ)   -- these are indices into traversed_nodes
(untraversed_neighbours : list ℕ) -- these are indices into untraversed_nodes, which does change!

structure partial_graph (α : Type u) :=
(traversed_vertices : list (traversed_vertex_data α))    -- we only ever append to this list, so indices are stable 
(untraversed_vertices : list (untraversed_vertex_data α))
(nonempty : traversed_vertices ≠ [])

variable {α : Type u}

def partial_graph.current_vertex (g : partial_graph α) := g.traversed_vertices.length
def partial_graph.current_vertex_data (g : partial_graph α) : traversed_vertex_data α := g.traversed_vertices.last g.nonempty

-- we're only ever adding vertices which are neighbours of the last traversed vertex
def add_new_untraversed_vertex (g : partial_graph α) (a : α) := {
  untraversed_vertices := g.untraversed_vertices ++ [⟨ a, g.traversed_vertices.length - 1, g.current_vertex_data.depth + 1⟩]
  ..g
}

def update_traversed_vertex (g : partial_graph α) (just_traversed : ℕ) (n : ℕ) :=
match g.traversed_vertices.nth n with
| none := g
| (some d) := let new_traversed_neighbours := d.traversed_neighbours ++ [g.current_vertex] in
              let new_untraversed_neighbours := d.untraversed_neighbours.erase just_traversed in
              if d.depth > g.current_vertex_data.depth + 1 then
                {
                  traversed_vertices := g.traversed_vertices.update_nth n {
                                                                            traversed_neighbours := new_traversed_neighbours,
                                                                            untraversed_neighbours := new_untraversed_neighbours,
                                                                            parent := g.current_vertex, 
                                                                            depth := g.current_vertex_data.depth + 1, 
                                                                          .. d},
                  nonempty := sorry,
                .. g }
              else 
                {
                  traversed_vertices := g.traversed_vertices.update_nth n {
                                                                            traversed_neighbours := new_traversed_neighbours,
                                                                            untraversed_neighbours := new_untraversed_neighbours,
                                                                          .. d},
                  nonempty := sorry,
                .. g }
end

def update_untraversed_vertex (g : partial_graph α) (n : ℕ) :=
match g.untraversed_vertices.nth n with
| none := g
| (some d) := if d.depth > g.current_vertex_data.depth + 1 then
                { untraversed_vertices := g.untraversed_vertices.update_nth n { parent := g.current_vertex, depth := g.current_vertex_data.depth + 1, .. d}, .. g }
              else 
                g
end

def add_traversed_neighbour_to_current_vertex (g : partial_graph α) (n : ℕ) :=
match g.traversed_vertices.nth n with
| none := g
| (some d) := {
  traversed_vertices := g.traversed_vertices.update_nth g.current_vertex { traversed_neighbours := d.traversed_neighbours ++ [n], ..d },
  nonempty := sorry,
  .. g
}
end

def add_untraversed_neighbour_to_current_vertex (g : partial_graph α) (n : ℕ) :=
match g.traversed_vertices.nth n with
| none := g
| (some d) := {
  traversed_vertices := g.traversed_vertices.update_nth g.current_vertex { untraversed_neighbours := d.untraversed_neighbours ++ [n], ..d },
  nonempty := sorry,
  .. g
}
end

def mark_vertex_traversed_1 (n : ℕ) (k : ℕ) (v : traversed_vertex_data α) : traversed_vertex_data α :=
{
traversed_neighbours   := if n ∈ v.untraversed_neighbours then v.traversed_neighbours ++ [k] else v.traversed_neighbours,
untraversed_neighbours := (v.untraversed_neighbours.remove_all [n]).map(λ m, if m > n then m-1 else m),
..v
}

@[simp] lemma append_eq_nil {α} (p q : list α) : (p ++ q) = [] ↔ p = [] ∧ q = [] :=
begin
split,
{
  intros,
  split,
  apply list.eq_nil_of_prefix_nil, rw ← a, simp, 
  apply list.eq_nil_of_suffix_nil, rw ← a, simp,
},
{
  intros,
  induction a,
  rw [a_left, a_right],
  refl,
}
end

def mark_vertex_traversed_2 (n : ℕ) (g : partial_graph α) : partial_graph α :=
match g.untraversed_vertices.nth n with
| none := g
| (some d) := {
                traversed_vertices := g.traversed_vertices.map (mark_vertex_traversed_1 n g.traversed_vertices.length) ++ [{ traversed_neighbours := [], untraversed_neighbours := [], .. d}],
                untraversed_vertices := g.untraversed_vertices.remove_nth n,
                nonempty := by simp,
              }
end

/- We've just marked a vertex as traversed, and need to add edges. -/
def process_neighbour [decidable_eq α] (just_traversed : ℕ) (g : partial_graph α) (a : α) : partial_graph α :=
match (g.traversed_vertices.map(λ d : traversed_vertex_data α, d.label)).indexes_of a with
| (n :: _) := -- `a` has already been traversed
              add_traversed_neighbour_to_current_vertex (update_traversed_vertex g just_traversed n) n
| [] := -- `a` has not already been traversed
        match (g.untraversed_vertices.map(λ d : untraversed_vertex_data α, d.label)).indexes_of a with
        | (n :: _) := -- `a` has already been listed as untraversed
                      add_untraversed_neighbour_to_current_vertex (update_untraversed_vertex g n) n
        | [] := -- we've never seen `a` before!
                add_untraversed_neighbour_to_current_vertex (add_new_untraversed_vertex g a) g.untraversed_vertices.length
        end
end

def traverse [decidable_eq α] (neighbours : α → list α) (n : ℕ) (g : partial_graph α) : partial_graph α :=
match g.untraversed_vertices.nth n with
| none := g
| (some d) := --let ns := (neighbours d.label).map (λ n, (n, g.traversed_vertices.find_indexes (λ d, d.label = n), g.untraversed_vertices.find_indexes (λ d, d.label = n))) in
              let g' := mark_vertex_traversed_2 n g in
              (neighbours d.label).foldl (process_neighbour n) g'
end              

def partial_graph.root [decidable_eq α] (neighbours : α → list α) (a : α) : partial_graph α := 
let ns := (neighbours a).erase a in
{
  traversed_vertices := [{ label := a, parent := 0, depth := 0, traversed_neighbours := [], untraversed_neighbours := list.range ns.length}],
  untraversed_vertices := ns.map(λ n, { label := n, parent := 0, depth := 1 }),
  nonempty := by simp
}

def breadth_first_search [decidable_eq α] (neighbours : α → list α) (a : α) : ℕ → partial_graph α
| 0 := partial_graph.root neighbours a
| (n+1) := traverse neighbours 0 (breadth_first_search n)

#eval (breadth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).traversed_vertices.map(λ v : traversed_vertex_data (ℕ × ℕ), v.label)
#eval (breadth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).untraversed_vertices.map(λ v : untraversed_vertex_data (ℕ × ℕ), v.label)

-- knights' moves
#eval (breadth_first_search (λ p : ℤ × ℤ, [(p.1+2,p.2+1),(p.1+2,p.2-1),(p.1-2,p.2+1),(p.1-2,p.2-1),(p.1+1,p.2+2),(p.1+1,p.2-2),(p.1-1,p.2+2),(p.1-1,p.2-2)]) (0,0) 100).traversed_vertices.map(λ v : traversed_vertex_data (ℤ × ℤ), (v.label, v.depth))


namespace tactic

namespace interactive
open interactive interactive.types expr


private meta def list_while' {α} (f : ℕ → tactic α) (P : ℕ → α → bool) : ℕ → α → bool → list α → tactic (list α)
| _ _ ff t := pure t
| n a tt t := (do g ← f (n+1), list_while' (n+1) g (P (n+1) g) (a :: t)) <|> pure (a :: t)

meta def list_while {α} (f : ℕ → tactic α) (P : ℕ → α → bool) : tactic (list α) :=
do 
  g ← f 0,
  r ← (list_while' f P 0 g (P 0 g) []),
  pure r.reverse

meta def ppexpr := expr × string × ℕ 

meta def to_ppexpr (e : expr) : tactic ppexpr :=
do pp ← pp e,
   let pp := pp.to_string,
   pure ⟨ e, pp, pp.to_nat ⟩ -- to_nat is not a good hash function!

meta structure rewrite_chain (source : ppexpr) (target : ppexpr)  :=
(chain : list (expr × ℕ))
(proof : expr)

meta def compose_rewrite_chain {e1 e2 e3 : ppexpr} (c1 : rewrite_chain e1 e2) (c2 : rewrite_chain e2 e3) : rewrite_chain e1 e3 :=
{
  chain := c1.chain ++ c2.chain,
  proof := sorry
}

def flatten {α} : list (list α) → list α
| [] := []
| (h :: t) := h ++ (flatten t)

meta def all_rewrites' (rs: list expr) (source : ppexpr): tactic (list (Σ target : ppexpr, (rewrite_chain source target))) :=
do table ← rs.mmap $ λ e,
   (do results ← (list_while (λ n, do v ← tactic.rewrite e source.1 {occs := occurrences.pos [n+1]}, pure (n, v)) (λ n x, tt)),
      results.mmap (λ result, do
        let (n, new_t, prf, _) := result,
        trace ((e, n), new_t),
        new_t ← to_ppexpr new_t,
        pure (⟨ new_t, { chain := [(e, n)], proof := prf }⟩ : Σ target : ppexpr, rewrite_chain source target))),
   pure (flatten table)  

meta def all_rewrites (rs : list expr) {source target : ppexpr} (chain : rewrite_chain source target) : tactic (list (Σ target' : ppexpr, (rewrite_chain source target'))) :=
do one_step ← all_rewrites' rs target,
   pure (one_step.map $ λ c, ⟨ c.1, compose_rewrite_chain chain c.2 ⟩)

meta structure rewrite_search_state (source : ppexpr) :=
(chains : hash_map ppexpr (λ target : ppexpr, (rewrite_chain source target)))
(unsearched : list ppexpr)

meta def empty_search_state (source : ppexpr) : tactic (rewrite_search_state source) :=
{
  chains := hash_map.of_list [⟨ source, ({ chain := [], proof := sorry } : rewrite_chain source source) ⟩] (λ e, e.2.2),
  unsearched := [source]
}

meta def all_rewrites_at (rs : list expr) {source} (state : rewrite_search_state source) (target : ppexpr) : tactic (rewrite_search_state source) :=
match state.chains.find target with
| none     := pure state
| (some c) := do results ← all_rewrites rs c,
                 let new_results := (results.filter $ λ p, ¬ state.chains.contains p.1),
                 pure {
                  chains := hash_map.insert_all new_results state.chains,
                  unsearched := (state.unsearched.erase target) ++ new_results.map (λ p, p.1)
                }
end

meta def all_rewrites_at_choice (rs : list expr) {source} (state : rewrite_search_state source) (choice : list ppexpr → tactic (option ppexpr)) : tactic (rewrite_search_state source) :=
do some target ← choice (state.unsearched) | pure state,
   all_rewrites_at rs state target

meta def breadth_first_rewrite_search' (rs : list expr) (source : ppexpr) : ℕ → tactic (rewrite_search_state source)
| 0       := empty_search_state source
| (n + 1) := do previous ← breadth_first_rewrite_search' n,
                if previous.unsearched.empty then
                  pure previous
                else
                  all_rewrites_at_choice rs previous (λ l, pure (l.head))

meta def breadth_first_rewrite_search (rs : list expr) (source : expr) : tactic (rewrite_search_state source) :=
breadth_first_rewrite_search' rs source 10

meta def rw_search (rs: parse rw_rules) (e : tactic expr := target): tactic unit :=
do rs ← rs.rules.mmap $ λ r, to_expr' r.rule,
   t ← e,
   breadth_first_rewrite_search rs t,
   skip

meta def rw_results (rs: parse rw_rules) (e : tactic expr := target): tactic (Σ source : expr, (list (Σ target : expr, (rewrite_chain source target)))) :=
do rs ← rs.rules.mmap $ λ r, to_expr' r.rule,
   t ← e,
   result ← all_rewrites' rs t,
   pure ⟨ t, result ⟩

end interactive
end tactic

open tactic.interactive

private lemma foo : [0] = [1] := sorry
private lemma bar : [2] = [1] := sorry

private lemma qux : [[0],[0]] = [[2],[2]] :=
begin
rw_search [foo,bar],
rw_results [foo,bar],
rw [foo] {occs := occurrences.pos [1]},
rw ← bar,
end