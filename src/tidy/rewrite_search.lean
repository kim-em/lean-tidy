import data.list
import data.hash_map

open lean
open lean.parser

universes t u v w

/-
A `partial_graph` represents a partial traversal of a graph, along with a tentative shortest path tree.
Each vertex of the graph is labelled by an `β`.
We also record along with each vertex its parent (this may be revised later, as more of the graph is traversed)
as an index into the prefix-immutable list of traversed vertices.
Along with the parent we record some 'descent_data' of some arbitrary type `γ`,
which we think of as recording how the vertex was generated from its parent (which also may be revised).
At each vertex we record the (current) depth to the root. We use this to decide whether to update parentage data when
the vertex is rediscovered.
-/

structure vertex_data (α : Type t) (β : Type u) (γ : Type v) :=
(compare_on : α)
(data : β)
(descent_data : γ)

structure untraversed_vertex_data (α : Type t) (β : Type u) (γ : Type v) :=
(data : vertex_data α β γ)
(parent : ℕ)
(depth : ℕ)

structure traversed_vertex_data (α : Type t) (β : Type u) (γ : Type v) extends untraversed_vertex_data α β γ :=
(traversed_neighbours : list ℕ)   -- these are indices into traversed_vertices
(untraversed_neighbours : list ℕ) -- these are indices into untraversed_vertices, which does change!

structure partial_graph (α : Type t) (β : Type u) (γ : Type v) :=
(traversed_vertices : list (traversed_vertex_data α β γ))    -- we only ever append to this list, so indices are stable 
(untraversed_vertices : list (untraversed_vertex_data α β γ))
(nonempty : traversed_vertices ≠ [])

attribute [simp] partial_graph.nonempty

variable {α : Type u}
variable {β : Type u}
variable {γ : Type v}

def partial_graph.current_vertex (g : partial_graph α β γ) := g.traversed_vertices.length
def partial_graph.current_vertex_data (g : partial_graph α β γ) := g.traversed_vertices.last g.nonempty

-- we're only ever adding vertices which are neighbours of the last traversed vertex
def add_new_untraversed_vertex (g : partial_graph α β γ) (data : vertex_data α β γ) := {
  untraversed_vertices := g.untraversed_vertices ++ [⟨ data, g.traversed_vertices.length - 1, g.current_vertex_data.depth + 1⟩]
  ..g
}

@[simp] lemma update_nth_empty {β} (l : list β) (n : ℕ) (a : β) : l.update_nth n a = [] ↔ l = [] :=
begin
split,
{
  induction l,
  unfold list.update_nth,
  intros, assumption,
  induction n,
  unfold list.update_nth,
  intros,
  contradiction,
  unfold list.update_nth,
  intros,
  contradiction
},
{
  intros,
  rw a_1,
  unfold list.update_nth,
}
end

def update_traversed_vertex (g : partial_graph α β γ) (just_traversed : ℕ) (previously_traversed : ℕ) (descent_data : γ) :=
match g.traversed_vertices.nth previously_traversed with
| none := g
| (some d) := let new_traversed_neighbours := d.traversed_neighbours ++ [g.current_vertex] in
              let new_untraversed_neighbours := d.untraversed_neighbours.erase just_traversed in
              if d.depth > g.current_vertex_data.depth + 1 then
                {
                  traversed_vertices := g.traversed_vertices.update_nth previously_traversed {
                                                                            data := { descent_data := descent_data, .. d.data },
                                                                            traversed_neighbours := new_traversed_neighbours,
                                                                            untraversed_neighbours := new_untraversed_neighbours,
                                                                            parent := g.current_vertex, 
                                                                            depth := g.current_vertex_data.depth + 1
                                                                          },
                  nonempty := by simp,
                .. g }
              else 
                {
                  traversed_vertices := g.traversed_vertices.update_nth previously_traversed {
                                                                            traversed_neighbours := new_traversed_neighbours,
                                                                            untraversed_neighbours := new_untraversed_neighbours,
                                                                          .. d},
                  nonempty := by simp,
                .. g }
end

def update_untraversed_vertex (g : partial_graph α β γ) (n : ℕ) :=
match g.untraversed_vertices.nth n with
| none := g
| (some d) := if d.depth > g.current_vertex_data.depth + 1 then
                { untraversed_vertices := g.untraversed_vertices.update_nth n { parent := g.current_vertex, depth := g.current_vertex_data.depth + 1, .. d}, .. g }
              else 
                g
end

def add_traversed_neighbour_to_current_vertex (g : partial_graph α β γ) (n : ℕ) :=
match g.traversed_vertices.nth n with
| none := g
| (some d) := {
  traversed_vertices := g.traversed_vertices.update_nth g.current_vertex { traversed_neighbours := d.traversed_neighbours ++ [n], ..d },
  nonempty := by simp,
  .. g
}
end

def add_untraversed_neighbour_to_current_vertex (g : partial_graph α β γ) (n : ℕ) :=
match g.traversed_vertices.nth n with
| none := g
| (some d) := {
  traversed_vertices := g.traversed_vertices.update_nth g.current_vertex { untraversed_neighbours := d.untraversed_neighbours ++ [n], ..d },
  nonempty := by simp,
  .. g
}
end

def mark_vertex_traversed_1 (n : ℕ) (k : ℕ) (v : traversed_vertex_data α β γ) : traversed_vertex_data α β γ :=
{
traversed_neighbours   := if n ∈ v.untraversed_neighbours then v.traversed_neighbours ++ [k] else v.traversed_neighbours,
untraversed_neighbours := (v.untraversed_neighbours.remove_all [n]).map(λ m, if m > n then m-1 else m),
..v
}

@[simp] lemma append_eq_nil {β} (p q : list β) : (p ++ q) = [] ↔ p = [] ∧ q = [] :=
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

def mark_vertex_traversed_2 (n : ℕ) (g : partial_graph α β γ) : partial_graph α β γ :=
match g.untraversed_vertices.nth n with
| none := g
| (some d) := {
                traversed_vertices := g.traversed_vertices.map (mark_vertex_traversed_1 n g.traversed_vertices.length) ++ [{ traversed_neighbours := [], untraversed_neighbours := [], .. d}],
                untraversed_vertices := g.untraversed_vertices.remove_nth n,
                nonempty := by simp,
              }
end

/- We've just marked a vertex as traversed, and need to add edges. -/
def process_neighbour [decidable_eq α] (just_traversed : ℕ) (g : partial_graph α β γ) (vertex : vertex_data α β γ) : partial_graph α β γ:=
match (g.traversed_vertices.map(λ d : traversed_vertex_data α β γ, d.data.compare_on)).indexes_of (vertex.compare_on) with
| (n :: _) := -- `a` has already been traversed
              add_traversed_neighbour_to_current_vertex (update_traversed_vertex g just_traversed n vertex.descent_data) n
| [] := -- `a` has not already been traversed
        match (g.untraversed_vertices.map(λ d : untraversed_vertex_data α β γ, d.data.compare_on)).indexes_of (vertex.compare_on) with
        | (n :: _) := -- `a` has already been listed as untraversed
                      add_untraversed_neighbour_to_current_vertex (update_untraversed_vertex g n) n
        | [] := -- we've never seen `a` before!
                add_untraversed_neighbour_to_current_vertex (add_new_untraversed_vertex g vertex) g.untraversed_vertices.length
        end
end

variable {m : Type max u v → Type max u v}

def traverse [decidable_eq α] [monad m] (neighbours : β → m (list (vertex_data α β γ))) (n : ℕ) (g : partial_graph α β γ) : m (partial_graph α β γ) :=
match g.untraversed_vertices.nth n with
| none := pure g
| (some d) := let g' := mark_vertex_traversed_2 n g in
              do ns ← neighbours d.data.data,
                 pure (ns.foldl (process_neighbour n) g')
end              

def partial_graph.root [decidable_eq α] [monad m] (neighbours : β → m (list (vertex_data α β γ))) (vertex : vertex_data α β γ) : m (partial_graph α β γ) := 
do
 ns ← neighbours vertex.data,
 let ns := ns.filter (λ p, p.compare_on ≠ vertex.compare_on),
  pure {
    traversed_vertices := [{ data := vertex, parent := 0, depth := 0, traversed_neighbours := [], untraversed_neighbours := list.range ns.length}],
    untraversed_vertices := ns.map(λ n, { data := n, parent := 0, depth := 1 }),
    nonempty := by simp
  }

def breadth_first_search_monadic [decidable_eq α] [monad m] (neighbours : β → m (list (vertex_data α β γ))) (vertex : vertex_data α β γ) : ℕ → m (partial_graph α β γ)
| 0 := partial_graph.root neighbours vertex
| (n+1) := do previous ← breadth_first_search_monadic n,
              traverse neighbours 0 previous


def depth_first_search_monadic [decidable_eq α] [monad m] (neighbours : β → m (list (vertex_data α β γ))) (vertex : vertex_data α β γ) : ℕ → m (partial_graph α β γ)
| 0 := partial_graph.root neighbours vertex
| (n+1) := do previous ← depth_first_search_monadic n,
              traverse neighbours (previous.untraversed_vertices.length - 1) previous

instance id_monad : monad id := 
begin
refine {
  bind := λ _ _ a f, f a,
  map := λ _ _ f, f,
  pure := λ _ a, a,
  ..
},
intros, refl, intros, refl, intros, refl
end

def breadth_first_search [decidable_eq β] (neighbours : β → list β) (a : β) : ℕ → partial_graph β β ℕ := @breadth_first_search_monadic β β ℕ id _ _ (λ x, (neighbours x).enum.map(λ p, ⟨ p.2, p.2, p.1 ⟩)) ⟨ a, a, 0 ⟩
def depth_first_search [decidable_eq β] (neighbours : β → list β) (a : β) : ℕ → partial_graph β β ℕ := @depth_first_search_monadic β β ℕ id _ _ (λ x, (neighbours x).enum.map(λ p, ⟨ p.2, p.2, p.1 ⟩)) ⟨ a, a, 0 ⟩

#eval (breadth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).traversed_vertices.map(λ v : traversed_vertex_data (ℕ × ℕ) (ℕ × ℕ) ℕ, v.data.data)
#eval (breadth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).untraversed_vertices.map(λ v : untraversed_vertex_data (ℕ × ℕ) (ℕ × ℕ) ℕ, v.data.data)

#eval (depth_first_search (λ p : ℕ × ℕ, [(p.1+1,p.2),(p.1,p.2+1)]) (0,0) 15).traversed_vertices.map(λ v : traversed_vertex_data (ℕ × ℕ) (ℕ × ℕ) ℕ, v.data.data)

-- knights' moves
def knights := (λ p : ℤ × ℤ, [(p.1+2,p.2+1),(p.1+2,p.2-1),(p.1-2,p.2+1),(p.1-2,p.2-1),(p.1+1,p.2+2),(p.1+1,p.2-2),(p.1-1,p.2+2),(p.1-1,p.2-2)])
#eval (breadth_first_search knights (0,0) 20).traversed_vertices.map(λ v : traversed_vertex_data (ℤ × ℤ) (ℤ × ℤ) ℕ, (v.data.data, v.data.descent_data))
#eval (depth_first_search knights (0,0) 20).traversed_vertices.map(λ v : traversed_vertex_data (ℤ × ℤ) (ℤ × ℤ) ℕ, (v.data.data, v.data.descent_data))

namespace tactic

namespace interactive
open interactive interactive.types expr


private meta def list_while' {β} (f : ℕ → tactic β) (P : ℕ → β → bool) : ℕ → β → bool → list β → tactic (list β)
| _ _ ff t := pure t
| n a tt t := (do g ← f (n+1), list_while' (n+1) g (P (n+1) g) (a :: t)) <|> pure (a :: t)

meta def list_while {β} (f : ℕ → tactic β) (P : ℕ → β → bool) : tactic (list β) :=
do 
  g ← f 0,
  r ← (list_while' f P 0 g (P 0 g) []),
  pure r.reverse

def flatten {β} : list (list β) → list β
| [] := []
| (h :: t) := h ++ (flatten t)

meta def all_rewrites (rs: list expr) (source : expr) : tactic (list (string × (expr × ℕ × ℕ × expr))) :=
do table ← rs.enum.mmap $ λ e,
   (do results ← (list_while (λ n, do v ← tactic.rewrite e.2 source {occs := occurrences.pos [n+1]}, pure (n, v)) (λ n x, tt)),
      results.mmap (λ result, do
        let (n, target, proof, _) := result,
        trace ((e, n), target),
        pp ← pp target,
        let pp := pp.to_string,
        pure (pp, (target, e.1, n, proof)))),
   pure (flatten table) 

meta def rewrite_search (rs : list expr) (start : expr) := 
do pp ← pp start,
   let pp := pp.to_string,
breadth_first_search_γic (all_rewrites rs) pp (expr, 0, 0, sorry)

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