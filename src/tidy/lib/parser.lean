import .interaction_monad

namespace lean.parser

open lean interactive.types

meta def opt_single_or_list {α : Type} (ps : lean.parser α) : lean.parser (list α) :=
  list_of ps <|> ((λ h, list.cons h []) <$> ps) <|> return []

meta def cur_options : lean.parser options := λ s, interaction_monad.result.success (parser_state.options s) s

meta def emit_command_here (str : string) : lean.parser string := do
  (_, left) ← with_input command_like str,
  return left

meta def emit_code_here (str : string) : lean.parser unit := do
  left ← emit_command_here str,
  if left.length = 0 then return ()
  else tactic.fail "did not parse all of passed code"

-- TODO polish up the `mk_*` family to be more robust, to the point where we take
-- the same arguments as environment.add

meta def var_string (v : name × expr) : string :=
  "(" ++ to_string v.1 ++ " : " ++ to_string v.2 ++ ")"

-- FIXME at the moment attribute errors cause a red line at the top of the window
-- TODO support more compicated annotation syntax.
meta def mk_definition_here_raw (n : name) (vars : list (name × expr)) (type : option expr) (value : string) (is_meta : bool := ff) (annotations : list string := []) : lean.parser unit :=
  emit_code_here $
    (if annotations.length = 0 then "" else "@" ++ annotations.to_string ++ " ")
    ++ (if is_meta then "meta " else "") ++ "def " ++ to_string n
    ++ string.intercalate " " (vars.map var_string)
    ++ match type with | none := "" | some type := " : " ++ to_string type end
    ++ " := " ++ to_string value

meta def mk_definition_here (n : name) (vars : list (name × expr)) (type : option expr) (value : expr) (is_meta : bool := ff) (annotations : list name := []) : lean.parser unit :=
  mk_definition_here_raw n vars type (to_string value) is_meta (annotations.map to_string)

-- TODO implement `mk_attribute_here`/`mk_attribute_here_raw`

open name

meta def chop_reserved_name (new_top_level : name := anonymous) : name → name
| anonymous                := anonymous
| (mk_numeral n anonymous) := mk_string ("n" ++ to_string n)     new_top_level
| (mk_string  s anonymous) := mk_string s.to_list.tail.as_string new_top_level
| (mk_numeral n pfx)       := mk_string ("n" ++ to_string n) $ chop_reserved_name pfx
| (mk_string  s pfx)       := mk_string s                    $ chop_reserved_name pfx

meta def mk_user_fresh_name (pfx : string := "") (sfx : string := "") : tactic name := do
  let pfx_name := if pfx.length = 0 then anonymous else mk_string pfx anonymous,
  chopped ← chop_reserved_name pfx_name <$> tactic.mk_fresh_name,
  return $ if sfx.length = 0 then chopped else mk_string sfx chopped

meta inductive boxed_result (α : Type)
| success : α → boxed_result
| failure : format → boxed_result

meta def of_tactic_safe {α : Type} (t : tactic α) : lean.parser α := do
  let tac : tactic (boxed_result α) := interaction_monad_orelse_intercept_safe (do
    r ← t,
    return $ boxed_result.success r
  )
  (λ e ref, return $ boxed_result.failure _ $ match e with
    | some e := e ()
    | none   := "tactic failed"
    end
  )
  (boxed_result.failure _ "tactic failed while handling tactic failed!"),
  ret ← of_tactic tac,
  match ret with
  | boxed_result.success ret := return ret
  | boxed_result.failure _ reason := interaction_monad.fail reason
  end

end lean.parser