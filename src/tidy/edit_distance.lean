def edit_distance_naive {α} [decidable_eq α] : list α → list α → ℕ
| [] l := l.length
| l [] := l.length
| (a :: b) (c :: d) := if a = c then 
                         edit_distance_naive b d 
                       else 
                         1 + min (min (edit_distance_naive (a :: b) d) (edit_distance_naive b (c :: d))) (edit_distance_naive b d)

-- PROJECT it would be great to be able to specify a maximum distance here, and bail out if we got beyond that.
-- The type signature would be:
--   def edit_distance {α} [decidable_eq α] (l₁ l₂ : list α) (max : option ℕ) : option ℕ :=
-- with a value of `none` meaning that `max` was `some L`, and the edit distance is at least `L`.

def edit_distance.aux {α} [decidable_eq α] (a : α) (b : list α) : list α → ℕ → list ℕ → ℕ × list ℕ
| []     _  _  := (b.length + 1, [])
| (c::d) _  [] := (0, []) -- won't happen
| (c::d) bc (bd::bd') :=
  let (ad, ad') := edit_distance.aux d bd bd' in
  (if a = c then bd else 1 + min (min ad bc) bd, ad::ad')

def edit_distance.aux' {α} [decidable_eq α] : list α → list α → ℕ × list ℕ
| []     []     := (0, [])
| []     (c::d) := let (n, ih) := edit_distance.aux' [] d in (n+1, n::ih)
| (a::b) l      := let (n, ih) := edit_distance.aux' b l in
  edit_distance.aux a b l n ih

def edit_distance {α} [decidable_eq α] (l₁ l₂ : list α) : ℕ :=
(edit_distance.aux' l₁ l₂).1

-- PROJECT some lemmas that show edit_distance behaves correctly?
-- PROJECT edit distance with transpositions?
-- PROJECT edit distance on trees?

def list.split_on_aux {α} [decidable_eq α] (a : α) : list α → list α → list (list α) 
| [] l       := [l.reverse]
| (h :: t) l := if h = a then
                  l.reverse :: (list.split_on_aux t [])
                else
                  list.split_on_aux t (h :: l)

def list.split_on {α} [decidable_eq α] (a : α) : list α → list (list α) 
| l := list.split_on_aux a l []

def string.split_on (c : char) (s : string) := (s.to_list.split_on c).map(λ l, l.as_string)

def string_edit_distance (s₁ s₂ : string) := edit_distance s₁.to_list s₂.to_list
def word_edit_distance (s₁ s₂ : string) := edit_distance (s₁.split_on ' ') (s₂.split_on ' ')

-- #eval string_edit_distance "the quick brown fox" "jumped over the lazy dog"
-- #eval word_edit_distance "big oak flat" "oak big flat"

variables {α : Type} [decidable_eq α]

structure partial_edit_distance_data (α : Type) :=
(prefix_length : ℕ)
(suffix    : list α)
(distances : list ℕ) -- distances from the prefix of l₁ to each non-empty prefix of l₂

def empty_partial_edit_distance_data {α : Type} (l₁ l₂: list α) : partial_edit_distance_data α := ⟨ 0, l₁, (list.range l₂.length).map(λ n, n+1) ⟩

inductive edit_distance_progress (l₁: list α) (l₂: list α)
| exactly : ℕ → edit_distance_progress
| at_least : ℕ → partial_edit_distance_data α → edit_distance_progress

variables {l₁: list α} {l₂: list α} 

open edit_distance_progress

def triples (p : partial_edit_distance_data α) (l₂ : list α): list (ℕ × ℕ × α) := p.distances.zip ((p.prefix_length :: p.distances).zip l₂)

def update_edit_distance : edit_distance_progress l₁ l₂ → edit_distance_progress l₁ l₂ 
| (exactly l₁ l₂ n)    := exactly l₁ l₂ n
| (at_least l₁ l₂ n p) := match p.suffix with
  | []       := exactly l₁ l₂ p.distances.ilast
  | (h :: t) := let new_distances : ℕ × list ℕ := (triples p l₂).foldl (λ n : ℕ × list ℕ, λ t : ℕ × ℕ × α, let m := (if h = t.2.2 then t.2.1 else 1 + min (min (t.2.1) (t.1)) n.2.head) in (if m < n.1 then m else n.1, m :: n.2)) (p.prefix_length + 1, [p.prefix_length + 1]) in
                at_least l₁ l₂ new_distances.1 ⟨ p.prefix_length + 1, t, new_distances.2.reverse.drop 1 ⟩
end 

-- meta instance [has_to_format α] : has_repr (edit_distance_progress l₁ l₂) := {
--   repr := λ p, match p with
--   | exactly l₁ l₂ n := (format!"= {n}").to_string
--   | at_least l₁ l₂ n p := (format!"≥ {n}, {p.suffix}, {p.distances}").to_string
--   end
-- }

meta def edit_distance_core : edit_distance_progress l₁ l₂ → ℕ 
| (exactly _ _ n) := n
| (p@_) := edit_distance_core (update_edit_distance p)

meta def edit_distance' (l₁: list α) (l₂: list α) := edit_distance_core (at_least l₁ l₂ 0 (empty_partial_edit_distance_data l₁ l₂))

-- #eval edit_distance' [1,2,3,4] [1,2,3,4]

-- def f0 : partial_edit_distance_data ℕ := ⟨ 0, [7,8,9], [1,2,3,4,5] ⟩ 
-- def p0 : edit_distance_progress [7,8,9] [7,8,9,8,9] := at_least [7,8,9] [7,8,9,8,9]  0 f0

-- def p1 := update_edit_distance p0
-- def p2 := update_edit_distance p1
-- def p3 := update_edit_distance p2
-- def p4 := update_edit_distance p3
-- def p5 := update_edit_distance p4

-- #eval p0
-- #eval p1
-- #eval p2
-- #eval p3
-- #eval p4

