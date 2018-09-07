import data.option
import data.buffer

universe u

def list.contains {α : Type u} [decidable_eq α] (a : α) : list α → bool
| [] := ff
| (h :: rest) := if a = h then tt else rest.contains

def list.multiplex {α : Type u} : list α → list α → list α
| [] l := l
| l [] := l
| (a₁ :: l₁) (a₂ :: l₂) := [a₁, a₂].append $ l₁.multiplex l₂

def list.at {α : Type u} [inhabited α] (l : list α) (n : ℕ) : α :=
list.head $ option.to_list $ list.nth l n

private def list_set_at_aux {α : Type u} (val : α) : list α → list α → ℕ → list α
| _ [] _          := []
| l (a :: rest) 0 := l.append (val :: rest)
| l (a :: rest) k := list_set_at_aux (l.append [a]) rest (k - 1)

def list.set_at {α : Type u} (l : list α) (idx : ℕ) (val : α) : list α :=
  list_set_at_aux val [] l idx

def list.split_on_aux {α : Type u} [decidable_eq α] (a : α) : list α → list α → list (list α)
| [] l       := [l.reverse]
| (h :: t) l := if h = a then
                  l.reverse :: (list.split_on_aux t [])
                else
                  list.split_on_aux t (h :: l)

def list.split_on {α : Type u} [decidable_eq α] (a : α) : list α → list (list α)
| l := list.split_on_aux a l []

def list.erase_first_such_that {α : Type u} (f : α → Prop) [decidable_pred f] : list α → list α
| [] := []
| (h :: t) := if f h then t else (h :: t.erase_first_such_that)

def list.erase_such_that {α : Type u} (f : α → Prop) [decidable_pred f] : list α → list α :=
list.filter (λ x, ¬ f x)

def list.strip {α : Type u} [decidable_eq α] (l : list α) (v : α) : list α :=
  l.erase_such_that (λ c, c = v)

def list.stripl {α : Type u} [decidable_eq α] (l : list α) (vs : list α) : list α :=
  l.erase_such_that (λ c, c ∈ vs)

def char_buffer.from_list (l : list char) : char_buffer := buffer.nil.append_list l

def string.split_on (c : char) (s : string) := (s.to_list.split_on c).map (λ l, l.as_string)

