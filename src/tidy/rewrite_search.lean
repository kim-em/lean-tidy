import data.list
import data.hash_map
import .edit_distance

open lean
open lean.parser

universes t u v w

def list.flatten {β} : list (list β) → list β
| [] := []
| (h :: t) := h ++ (list.flatten t)


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

structure partial_graph_pair (α : Type t) (β : Type u) (γ : Type v) :=
(graph_1 : partial_graph α β γ)
(graph_2 : partial_graph α β γ)
(distances : list (list ℕ))  -- pairwise distances between untraversed vertices on each graph

variable {α : Type u}
variable {β : Type u}
variable {γ : Type v}

def partial_graph.current_vertex (g : partial_graph α β γ) := g.traversed_vertices.length
def partial_graph.current_vertex_data (g : partial_graph α β γ) := g.traversed_vertices.last g.nonempty

-- We have to use meta here because the recursion can't be justified without much more care.
meta def partial_graph.traversed_vertex_ancestry (g : partial_graph α β γ) : ℕ → list γ 
| 0 := []
| n := match g.traversed_vertices.nth n with
       | none := []
       | (some v) := v.data.descent_data :: (partial_graph.traversed_vertex_ancestry v.parent)
       end
meta def partial_graph.untraversed_vertex_ancestry (g : partial_graph α β γ) : ℕ → list γ 
| n := match g.untraversed_vertices.nth n with
       | none := []
       | (some v) := v.data.descent_data :: (partial_graph.traversed_vertex_ancestry g v.parent)
       end

-- we're only ever adding vertices which are neighbours of the last traversed vertex
def add_new_untraversed_vertex (g : partial_graph α β γ) (data : vertex_data α β γ) := {
  untraversed_vertices := g.untraversed_vertices ++ [⟨ data, g.traversed_vertices.length - 1, g.current_vertex_data.depth + 1⟩]
  ..g
}


-- TODO mathlib
@[simp] lemma update_nth_eq_nil {β} (l : list β) (n : ℕ) (a : β) : l.update_nth n a = [] ↔ l = [] :=
begin
split,
show list.update_nth l n a = list.nil → l = list.nil, 
{
  induction l,
  case list.nil {
    intros,
    assumption
  },
  case list.cons {
    induction n,
    all_goals { contradiction }
  }
},
-- show l = list.nil → list.update_nth l n a = list.nil,
{
  intros, simp *, refl
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

-- TODO mathlib
@[simp] lemma append_eq_nil {β} (p q : list β) : (p ++ q) = [] ↔ p = [] ∧ q = [] :=
begin
split,
show (p ++ q) = [] → p = [] ∧ q = [],
{
  intro h,
  split,
  apply list.eq_nil_of_prefix_nil, rw ← h, simp, 
  apply list.eq_nil_of_suffix_nil, rw ← h, simp,
},
show p = [] ∧ q = [] → p ++ q = [],
{
  intros h,
  rw [h.left, h.right],
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

def min_with_position : list ℕ → option (ℕ × ℕ)
| [] := none
| (h :: t) := let min := t.foldl min h in
              let p := (h :: t).index_of min in
              some (min, p)

def min_with_position_2 : list (list ℕ) → option (ℕ × ℕ × ℕ)
| l := match min_with_position l.flatten with
       | none := none
       | (some (min, _)) := let n := l.find_index (λ r, min ∈ r) in
                            match l.nth n with
                            | none := none -- impossible
                            | (some r) := some (min, n, r.index_of min)
                            end
       end

def pair_traverse [decidable_eq α] [monad m] (neighbours : β → m (list (vertex_data α β γ))) (distance : α → α → ℕ) (p : partial_graph_pair α β γ) : m (partial_graph_pair α β γ) :=
match min_with_position_2 p.distances with 
| none := /- we're done! -/ pure p
| (some (0, _, _)) := /- we're done! -/ pure p
| (some (min, x, y)) := do new_graph_1 ← traverse neighbours x p.graph_1,
                           new_graph_2 ← traverse neighbours y p.graph_2,
                           let old_distances := (p.distances.remove_nth x).map(λ r, r.remove_nth y),
                           let new_distances := ((new_graph_1.untraversed_vertices.enum).map $
                                                  λ p_i, (new_graph_2.untraversed_vertices.enum).map $
                                                    λ p_j, if h_i : p_i.1 < old_distances.length then
                                                            if h_j : p_j.1 < (old_distances.nth_le p_i.1 h_i).length then
                                                              (old_distances.nth_le p_i.1 h_i).nth_le p_j.1 h_j
                                                            else
                                                              distance p_i.2.data.compare_on p_j.2.data.compare_on
                                                           else
                                                             distance p_i.2.data.compare_on p_j.2.data.compare_on),
                           pure ⟨ new_graph_1, new_graph_2, new_distances ⟩
                                                    
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

def graph_pair_search_monadic [decidable_eq α] [monad m]
  (neighbours : β → m (list (vertex_data α β γ))) 
  (distance : α → α → ℕ) 
  (vertex_1 : vertex_data α β γ) 
  (vertex_2 : vertex_data α β γ) : ℕ → m (partial_graph_pair α β γ)
| 0 := do graph_1 ← partial_graph.root neighbours vertex_1,
          graph_2 ← partial_graph.root neighbours vertex_2,
          let distances := graph_1.untraversed_vertices.map $ λ v, graph_2.untraversed_vertices.map $ λ w, distance v.data.compare_on w.data.compare_on,
          pure ⟨ graph_1, graph_2, distances ⟩
| (n+1) := do previous ← graph_pair_search_monadic n,
              pair_traverse neighbours distance previous

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
(do 
  g ← f 0,
  r ← (list_while' f P 0 g (P 0 g) []),
  pure r.reverse) <|> pure []
 
meta def simp_as_rewrite (source : expr) : tactic (list (vertex_data string expr (ℕ × ℕ × expr))) :=
(do (s, u) ← tactic.mk_simp_set ff [] [],
   (target, proof) ← tactic.simplify s [] source {},
   pp ← pp target,
   let pp := pp.to_string,
   pure [ { vertex_data . compare_on := pp, data := target, descent_data := (0, 0, proof) } ]) <|> pure []

meta def all_rewrites (rs: list expr) (source : expr) : tactic (list (vertex_data string expr (ℕ × ℕ × expr))) :=
do table ← rs.enum.mmap $ λ e,
   (do results ← (list_while (λ n, do v ← tactic.rewrite e.2 source {occs := occurrences.pos [n+1]}, pure (n, v)) (λ n x, tt /- do we need to discard any? or just wait until rewrite fails? -/)),
      results.mmap (λ result, do
        let (n, target, proof, _) := result,
        -- trace ((e, n), target),
        pp ← pp target,
        let pp := pp.to_string,
        pure { vertex_data . compare_on := pp, data := target, descent_data := (e.1 + 1, n, proof) })),
   by_simp ← simp_as_rewrite source,
   pure (by_simp ++ table.flatten) 

meta def rewrite_search_core (rs : list expr) (n : ℕ) (start : expr) := 
do pp ← pp start,
   let pp := pp.to_string,
   @depth_first_search_monadic _ _ _ tactic _ _ (all_rewrites rs) ⟨ pp, start, (0, 0, start /- this should be refl or something... -/) ⟩ n

meta def rewrite_search (rs: parse rw_rules) (n : ℕ) (e : tactic expr := target): tactic unit :=
do rs ← rs.rules.mmap $ λ r, to_expr' r.rule,
   t ← e,
   result ← rewrite_search_core rs n t,
   trace (result.traversed_vertices.map (λ v : traversed_vertex_data _ _ _, v.data.compare_on)),
  --  trace (result.untraversed_vertices.map (λ v : untraversed_vertex_data _ _ _, v.data.compare_on)),
   skip

meta def rewrite_search_eq_core (rs : list expr) (n : ℕ) (e1 e2 : expr) := 
do pp1 ← pp e1,
   let pp1 := pp1.to_string,
   pp2 ← pp e2,
   let pp2 := pp2.to_string,
   @graph_pair_search_monadic _ _ _ tactic _ _ (all_rewrites rs) string_edit_distance ⟨ pp1, e1, (0, 0, e1 /- FIXME -/) ⟩ ⟨ pp2, e2, (0, 0, e2 /- FIXME -/) ⟩ n


meta def rewrite_search_eq (rs: parse rw_rules) (n : ℕ) : tactic unit :=
do rs ← rs.rules.mmap $ λ r, to_expr' r.rule,
   t ← target,
   (lhs, rhs) ← match t with
     | `(%%lhs = %%rhs) := pure (lhs, rhs)
     | _ := fail "goal is not an equality"
     end,
   result ← rewrite_search_eq_core rs n lhs rhs,
   trace (result.graph_1.untraversed_vertices.map (λ v : untraversed_vertex_data _ _ _, v.data.compare_on)),
   trace (result.graph_2.untraversed_vertices.map (λ v : untraversed_vertex_data _ _ _, v.data.compare_on)),
   trace result.distances,
   match min_with_position_2 result.distances with
   | none := fail "exhausted rewrites without reaching equality"
   | (some (0, x, y)) := do let a_1 := (result.graph_1.untraversed_vertex_ancestry x).map(λ p, p.2.2),
                            let a_2 := (result.graph_2.untraversed_vertex_ancestry y).map(λ p, p.2.2),
                            skip
   | (some (d, x, y)) := fail "ran out of time without reaching equality"
   end

end interactive
end tactic


open tactic.interactive

private lemma foo : [0] = [1] := sorry
private lemma bar : [2] = [1] := sorry

private lemma qux : [[0],[0]] = [[2],[2]] :=
begin
rewrite_search [foo, bar] 100,
rw [foo] {occs := occurrences.pos [1]},
rw ← bar,
rw [foo, ← bar],
end

private lemma turkle : [[0],[0]] = [[2],[2]] :=
begin
rewrite_search_eq [foo, bar] 2,
sorry
end
