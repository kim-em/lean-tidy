import data.option
import data.buffer

universes u v w

namespace list

private def min_rel_aux {α : Type u} (r : α → α → Prop) [decidable_rel r] (curr : α) : list α → α
| [] := curr
| (a :: rest) := if r a curr then a else curr

def min_rel {α : Type u} (l : list α) (r : α → α → Prop) [decidable_rel r] : option α :=
  match l with
  | [] := none
  | (a :: rest) := some $ min_rel_aux r a rest
  end

def min {α : Type u} (l : list α) [has_lt α] [@decidable_rel α has_lt.lt] : option α :=
  min_rel l has_lt.lt

def contains {α : Type u} [decidable_eq α] (a : α) : list α → bool
| [] := ff
| (h :: rest) := if a = h then tt else rest.contains

meta def erase_duplicates {α : Type u} [decidable_eq α] : list α → list α
| [] := []
| (x :: t) := (x :: erase_duplicates (t.filter $ λ a, a ≠ x))

def multiplex {α : Type u} : list α → list α → list α
| [] l := l
| l [] := l
| (a₁ :: l₁) (a₂ :: l₂) := [a₁, a₂].append $ l₁.multiplex l₂

private def set_at_aux {α : Type u} (val : α) : list α → list α → ℕ → list α
| _ [] _          := []
| l (a :: rest) 0 := l.append (val :: rest)
| l (a :: rest) k := set_at_aux (l.append [a]) rest (k - 1)

def set_at {α : Type u} (l : list α) (idx : ℕ) (val : α) : list α :=
  set_at_aux val [] l idx

def split_on_aux {α : Type u} [decidable_eq α] (a : α) : list α → list α → list (list α)
| [] l       := [l.reverse]
| (h :: t) l := if h = a then
                  l.reverse :: (split_on_aux t [])
                else
                  split_on_aux t (h :: l)

def split_on {α : Type u} [decidable_eq α] (a : α) : list α → list (list α)
| l := split_on_aux a l []

def erase_first_such_that {α : Type u} (f : α → Prop) [decidable_pred f] : list α → list α
| [] := []
| (h :: t) := if f h then t else (h :: t.erase_first_such_that)

def erase_such_that {α : Type u} (f : α → Prop) [decidable_pred f] : list α → list α :=
filter (λ x, ¬ f x)

def strip {α : Type u} [decidable_eq α] (l : list α) (v : α) : list α :=
  l.erase_such_that (λ c, c = v)

def stripl {α : Type u} [decidable_eq α] (l : list α) (vs : list α) : list α :=
  l.erase_such_that (λ c, c ∈ vs)

end list

def list.at {α : Type u} [inhabited α] (l : list α) (n : ℕ) : α :=
list.head $ option.to_list $ list.nth l n
