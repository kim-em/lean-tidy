universes u

meta inductive mllist (m : Type u → Type u) (α : Type u) : Type u
| nil {} : mllist
| cons : α → m mllist → mllist

namespace mllist

meta def fix {m : Type u → Type u} [alternative m]
  {α} (f : α → m α) : α → m (mllist m α)
| x := (λ a, cons a (fix a)) <$> f x <|> pure nil

meta def force {m} [monad m] {α} : mllist m α → m (list α)
| nil := pure []
| (cons a l) := list.cons a <$> (l >>= force)

meta def map {m} [monad m] {α β : Type u} (f : α → β) : mllist m α → m (mllist m β)
| nil := pure nil
| (cons a l) := do r ← l, return (cons (f a) (map r))

meta def mmap {m} [monad m] [alternative m] {α β : Type u} (f : α → m β) : mllist m α → m (mllist m β)
| nil := pure nil
| (cons a l) := do r ← l, (f a >>= λ b, return (cons b (mmap r))) <|> mmap r

end mllist
