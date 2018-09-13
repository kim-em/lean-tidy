namespace environment

meta def decl_omap {α : Type} (e : environment) (f : declaration → option α) : list α :=
  e.fold [] $ λ d l, match f d with
                     | some r := r :: l
                     | none := l
                     end

meta def decl_map {α : Type} (e : environment) (f : declaration → α) : list α :=
  e.decl_omap $ λ d, some (f d)

meta def get_decls (e : environment) : list declaration :=
  e.decl_map id

meta def get_decl_names (e : environment) : list name :=
  e.decl_map declaration.to_name

-- Warning, I have to compute a list of all of the declarations first.
meta def decl_ommap {α : Type} (e : environment) (f : declaration → tactic (option α)) : tactic (list α) :=
  e.get_decls.mfoldl (λ l d, do
    r ← f d,
    return $ match r with
    | some r := r :: l
    | none := l
    end
  ) []

end environment