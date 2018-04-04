import data.fintype

universes u v

inductive pempty : Type u

def empty_function            {α : Sort u} : empty → α :=                      begin intros, cases a, end
def empty_dependent_function  {Z : empty → Sort u} : Π i : empty, Z i :=       begin intros, cases i, end
def pempty_function           {α : Sort u} : pempty.{v} → α :=                 begin intros, cases a, end
def pempty_dependent_function {Z : pempty.{v} → Sort u} : Π i : pempty, Z i := begin intros, cases i, end

instance : decidable_eq pempty := λ a b, begin cases a, end

instance pempty_fintype : fintype pempty := {
  elems := [].to_finset,
  complete := begin intros, cases x, end
}