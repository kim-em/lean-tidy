import tidy.lib.parser

open lean.parser
open interactive

@[user_command]
meta def suggestion_cmd (d : decl_meta_info) (_ : parse $ tk "suggestion") : lean.parser unit := do
  bn ← opt_single_or_list ident,
  -- Implement option parsing here, e.g:
  -- tgt ← optional (tk "at" *> ident),
  n ← mk_user_fresh_name "suggestion" "s___",
  mk_definition_here_raw n [] none (bn.map $ λ s, "`" ++ to_string s).to_string tt ["suggest"]
