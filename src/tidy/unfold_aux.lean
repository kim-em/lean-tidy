open tactic

meta def expr.names_with_prefix (pre : name) (r : expr) : list name := 
r.fold [] $ λ e _ l,
  match e with
  | expr.const n _ := if n.get_prefix = pre then insert n l else l
  | _ := l
  end

meta def unfold_aux : tactic unit :=
do tgt ← target,
   name ← decl_name,
   let to_unfold := tgt.names_with_prefix name,
   guard (to_unfold ≠ []),
   dunfold to_unfold tgt >>= change,
   try `[dsimp]
