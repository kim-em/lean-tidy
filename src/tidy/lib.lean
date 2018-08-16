universe u

--FIXME the fact that we use this is really sad (ARRAYS DO IT)
def list_at {α : Type u} (default : α) : list α → ℕ → α
| [] _ := default -- FIXME catastrophic failure
| (a :: rest) k := if k = 0 then a else list_at rest (k - 1)

def list_set_at_aux {α : Type u} (val : α) : list α → list α → ℕ → list α
| _ [] _          := [] -- FIXME catastrophic failure
| l (a :: rest) 0 := l.append (val :: rest)
| l (a :: rest) k := list_set_at_aux (l.append [a]) rest (k - 1)

--FIXME the fact that we use this is really sad (ARRAYS DO IT)
def list_set_at {α : Type u} (l : list α) (idx : ℕ) (val : α) : list α :=
  list_set_at_aux val [] l idx

def list.split_on_aux {α : Type u} [decidable_eq α] (a : α) : list α → list α → list (list α) 
| [] l       := [l.reverse]
| (h :: t) l := if h = a then
                  l.reverse :: (list.split_on_aux t [])
                else
                  list.split_on_aux t (h :: l)

def list.split_on {α : Type u} [decidable_eq α] (a : α) : list α → list (list α) 
| l := list.split_on_aux a l []

def string.split_on (c : char) (s : string) := (s.to_list.split_on c).map(λ l, l.as_string)

def list.erase_such_that {α : Type u} (f : α → Prop) [decidable_pred f] : list α → list α
| [] := []
| (h :: t) := if f h then t else h :: t.erase_such_that
