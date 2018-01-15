import data.buffer.parser

open lean.parser tactic interactive parser

@[user_attribute] meta def field_lemma_attr : user_attribute :=
{ name := `field_lemma, descr := "This definition was automatically generated from a structure field by `make_lemma`." }

structure foo := 
  ( X : ℕ . skip )

#check foo.X
#print foo.X

meta def make_lemma (d : declaration) (new_name : name) : tactic unit :=
do (levels, type, value, reducibility, trusted) ← pure (match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    (levels, type, value, reducibility, trusted)
  | _ := undefined
  end),
  (s, u) ← mk_simp_set ff [] [],
  new_type ← (s.dsimplify [] type) <|> pure (type),
--   new_value ← mk_app ``cast [pr, value],
  updateex_env $ λ env, env.add (declaration.defn new_name levels new_type value reducibility trusted),
  field_lemma_attr.set new_name () tt

@[user_command] meta def make_lemma_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "make_lemma") : lean.parser unit :=
do old ← ident,
  d ← (do old ← resolve_constant old, get_decl old) <|>
    fail ("declaration " ++ to_string old ++ " not found"),
  do {
    tk "←" <|> tk "<-",
    aliases ← many ident,
    ↑(aliases.mmap' $ λ al, make_lemma d al) }

example : 1+ 1 =2 := by simp

make_lemma foo.X ← fooX

#check fooX
#print fooX