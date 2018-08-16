import data.pnat
import data.nat.basic

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

lemma nat.succ_pred (n : ℕ) (h : n ≠ 0) : nat.succ (nat.pred n) = n := 
begin
  cases n,
  contradiction,
  simp,
end

lemma fin.with_max (n m : ℕ) (h : m ≠ 0): fin m := 
⟨ min n (m-1), begin 
                 have p := min_le_right n (nat.pred m), 
                 have q := nat.lt_succ_of_le p, 
                 rw nat.succ_pred at q,
                 exact q,
                 assumption
               end ⟩

lemma pnat.succ_pred (n : pnat) : nat.succ (nat.pred n) = n := 
begin
  cases n with n h,
  cases n,
  have := lt_irrefl _ h ; contradiction,
  simp,
end

lemma fin.with_max' (n : ℕ) (m : pnat) : fin m := 
⟨ min n (m-1), begin 
                 have p := min_le_right n (nat.pred m), 
                 have q := nat.lt_succ_of_le p, 
                 rw nat.succ_pred at q,
                 exact q,
                 exact nat.pos_iff_ne_zero.mp m.property,
               end ⟩               