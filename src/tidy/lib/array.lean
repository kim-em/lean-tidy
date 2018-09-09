universes u v z

namespace array

--FIXME make this not garbage
meta def mmap_copy_aux {k : Type v → Type z} [monad k] {α : Type u} {β : Type v} {n m : ℕ} (f : α → k β) : ℕ → array n α → array m β → k (array m β)
| r x y := dite (r < n) (λ hn, dite (r < m) (λ hm, do
    let fn : fin n := ⟨r, hn⟩,
    let fm : fin m := ⟨r, hm⟩,
    v ← f $ x.read fn,
    y ← mmap_copy_aux (r + 1) x y,
    return $ y.write fm v
  ) (λ _, return y)) (λ _, return y)

meta def mmap_copy {k : Type v → Type z} [monad k] {α : Type u} {β : Type v} {n m : ℕ} (x : array n α) (y : array m β) (f : α → k β) : k (array m β) :=
  mmap_copy_aux f 0 x y

--FIXME make this not garbage
meta def map_copy_aux {α : Type u} {β : Type v} {n m : ℕ} (f : α → β) : ℕ → array n α → array m β → array m β
| r x y :=
begin
  by_cases hn : r < n,
  have fn : fin n := ⟨r, hn⟩,
  by_cases hm : r < m,
  have fm : fin m := ⟨r, hm⟩,
  exact ((map_copy_aux (r + 1) x y).write fm $ f (x.read fn)),
  exact y,
  exact y
end

meta def map_copy {α : Type u} {β : Type v} {n m : ℕ} (x : array n α) (y : array m β) (f : α → β) : array m β :=
  map_copy_aux f 0 x y

meta def copy {α : Type u} {n m : ℕ} (x : array n α) (y : array m α) : array m α :=
  map_copy x y (λ a, a)

--FIXME make this not garbage
def list_map_copy_from {α : Type u} {β : Type v} {n : ℕ} (x : array n β) (fn : α → β) : list α → ℕ → array n β
| [] m := x
| (a :: rest) m := dite (m < n) (λ h,
    let f : fin n := ⟨m, h⟩ in
    (list_map_copy_from rest (m + 1)).write f (fn a)
  ) (λ _, x)

def list_map_copy {α : Type u} {β : Type v} {n : ℕ} (x : array n β) (fn : α → β) (l : list α) : array n β :=
  list_map_copy_from x fn l 0

def list_copy {α : Type u} {n : ℕ} (x : array n α) (l : list α) : array n α :=
  list_map_copy x (λ a, a) l

end array