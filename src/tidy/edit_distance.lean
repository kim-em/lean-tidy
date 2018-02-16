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