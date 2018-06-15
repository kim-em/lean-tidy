import data.fintype

universes u v

@[derive decidable_eq]
inductive pempty : Type u

instance pempty_fintype : fintype pempty := {
  elems := [].to_finset,
  complete := begin intros, cases x, end
}

def empty_function            {α : Sort u} : empty → α :=                      begin intros, cases a, end
def empty_dependent_function  {Z : empty → Sort u} : Π i : empty, Z i :=       begin intros, cases i, end
def pempty_function           {α : Sort u} : pempty.{v} → α :=                 begin intros, cases a, end
def pempty_dependent_function {Z : pempty.{v} → Sort u} : Π i : pempty, Z i := begin intros, cases i, end