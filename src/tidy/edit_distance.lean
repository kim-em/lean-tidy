def edit_distance_naive {α} [decidable_eq α] : list α → list α → ℕ
| [] l := l.length
| l [] := l.length
| (a :: b) (c :: d) := if a = c then 
                         edit_distance_naive b d 
                       else 
                         1 + min (min (edit_distance_naive (a :: b) d) (edit_distance_naive b (c :: d))) (edit_distance_naive b d)

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

def string_edit_distance (s₁ s₂ : string) := edit_distance s₁.to_list s₂.to_list

#eval edit_distance (list.range 20) (list.range 20).reverse