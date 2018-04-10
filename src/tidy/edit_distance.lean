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

-- FIXME get this out of meta
meta def edit_distance_progress.to_string : edit_distance_progress l₁ l₂ → string
| (exactly _ _ k)    := (format!"= {k}").to_string
| (at_least _ _ k _) := (format!"≥ {k}").to_string

def triples (p : partial_edit_distance_data α) (l₂ : list α): list (ℕ × ℕ × α) := p.distances.zip ((p.prefix_length :: p.distances).zip l₂)

def update_edit_distance_one_step : edit_distance_progress l₁ l₂ → edit_distance_progress l₁ l₂ 
| (exactly l₁ l₂ n)    := exactly l₁ l₂ n
| (at_least l₁ l₂ n p) := match p.suffix with
  | []       := exactly l₁ l₂ p.distances.ilast
  | (h :: t) := let new_distances : ℕ × list ℕ := (triples p l₂).foldl (λ n : ℕ × list ℕ, λ t : ℕ × ℕ × α, let m := (if h = t.2.2 then t.2.1 else 1 + min (min (t.2.1) (t.1)) n.2.head) in (if m < n.1 then m else n.1, m :: n.2)) (p.prefix_length + 1, [p.prefix_length + 1]) in
                at_least l₁ l₂ new_distances.1 ⟨ p.prefix_length + 1, t, new_distances.2.reverse.drop 1 ⟩
end 

-- PROJECT for the enthusiastic: show these inductions are well-founded, and remove the metas

meta def update_edit_distance_until (m : ℕ) : edit_distance_progress l₁ l₂ → edit_distance_progress l₁ l₂ 
| (exactly l₁ l₂ n)    := exactly l₁ l₂ n
| (at_least l₁ l₂ n p) := if n > m then (at_least l₁ l₂ n p) else update_edit_distance_until (update_edit_distance_one_step (at_least l₁ l₂ n p))

meta def update_edit_distance : edit_distance_progress l₁ l₂ → edit_distance_progress l₁ l₂ 
| (exactly l₁ l₂ n)    := exactly l₁ l₂ n
| (at_least l₁ l₂ n p) := update_edit_distance_until n (at_least l₁ l₂ n p)

meta def edit_distance_core : edit_distance_progress l₁ l₂ → ℕ 
| (exactly _ _ n) := n
| (p@_) := edit_distance_core (update_edit_distance p)

meta def edit_distance' (l₁: list α) (l₂: list α) := edit_distance_core (at_least l₁ l₂ 0 (empty_partial_edit_distance_data l₁ l₂))


