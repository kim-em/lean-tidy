import data.fintype

universes u v

@[derive decidable_eq]
inductive pempty : Type u

instance pempty_fintype : fintype pempty := 
{ elems := [].to_finset,
  complete := begin intros, cases x, end }

-- def empty.fun   {α : Sort u}               : empty → α        := begin intros, cases a, end
-- def empty.dfun  {Z : empty → Sort u}      : Π i : empty, Z i  := begin intros, cases i, end
-- def pempty.fun  {α : Sort u}               : pempty.{v} → α   := begin intros, cases a, end
-- def pempty.dfun {Z : pempty.{v} → Sort u} : Π i : pempty, Z i := begin intros, cases i, end