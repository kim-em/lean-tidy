-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import data.buffer.parser

open lean.parser tactic interactive parser

@[user_attribute] meta def field_lemma_attr : user_attribute :=
{ name := `field_lemma, descr := "This definition was automatically generated from a structure field by `make_lemma`." }

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
  field_lemma_attr.set new_name () tt,
  (set_basic_attribute `simp new_name tt) <|> skip

private meta def name_lemma (n : name) :=
match n.components.reverse with
| last :: most := mk_str_name n.get_prefix (last.to_string ++ "_lemma")
| nil          := undefined
end

@[user_command] meta def make_lemma_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "make_lemma") : lean.parser unit :=
do old ← ident,
  d ← (do old ← resolve_constant old, get_decl old) <|>
    fail ("declaration " ++ to_string old ++ " not found"),
  do {
    make_lemma d (name_lemma old)
  }.

-- structure foo := 
--   ( X : ℕ . skip )

-- make_lemma foo.X

-- #check foo.X_lemma
