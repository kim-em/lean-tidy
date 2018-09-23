import tidy.lib.pretty_print
import tidy.lib.name
import tidy.lib.expr
import tidy.lib.parser

open lean.parser
open interactive

open exceptional
open declaration

namespace tidy.command

namespace rfl_lemma

structure config :=
(attrs : list string := ["simp"])
(priv  : bool := ff)
(trace : bool := ff)

open tactic

meta def handle_defn (lemma_name : string) (conf : config) (e : environment) (fn_name : name) (fn_us : list name) (fn_type : expr) (fn_val : expr) (field : name) : tactic string := do
  (obj_name, obj_name_levels, fn_type_app_vars) ← app.chop $ prod.snd fn_type.unroll_pi_params,
  (fn_val_params, fn_val_core) ← pure fn_val.unroll_lam_params,

  let proj_name := obj_name ++ field,
  let proj_prime_name := obj_name ++ field.append_suffix "'",

  pi ← e.is_projection proj_prime_name
    <|> e.is_projection proj_name
    <|> fail format!"There are no projections: {proj_prime_name}', nor {proj_prime_name}",
  (field_params, field_val) ← expr.unroll_lam_params <$> structure_instance.extract_field fn_val_core pi,

  field_proj ← mk_const proj_name >>= infer_type
    <|> fail format!"There is no identifier: {proj_name}",
  let field_proj_params := (prod.fst field_proj.unroll_pi_params).drop (pi.nparams + 1),
  let field_params := field_params.zip_with param.set_binder_info (field_proj_params.map param.to_binder_info),

  let lemma_params := fn_val_params ++ field_params,
  args ← param.list_to_args lemma_params,
  st_value ← pretty_print (param.instantiate field_val lemma_params) ff tt,

  attrs ← if ¬(conf.attrs.length = 0) then
            pp format!"@[{string.lconcat (conf.attrs.intersperse \", \")}] "
          else
            return "",
  let mods := if conf.priv then "private " else "",

  code ← pp format!"{attrs}{mods}lemma {lemma_name} {args} : ({fn_name} {param.list_to_invocation fn_val_params}).{field} {param.list_to_invocation field_params} = {st_value} := rfl",

  if conf.trace then
    tactic.trace code
  else skip,
  return code.to_string

meta def assert_not_declared (n : string) : tactic unit := do
  ret ← try_core $ resolve_constant $ mk_simple_name n,
  match ret with
  | some _ := tactic.fail format!"There is already an identifier \"{n}\" in the environment!"
  | none   := return ()
  end

meta def handle (conf : config) (obj_def : name) (field : name) : tactic string := do
  e ← tactic.get_env,
  obj_def ← tactic.resolve_constant obj_def
  <|> interaction_monad.fail format!"Could not resolve the identifier \"{obj_def}\"",
  match e.get obj_def with
  | exception _ f := do
    interaction_monad.fail format!"Could not retrieve the declaration associated with \"{obj_def}\" from the environment!"
  | success decl :=
    match decl with
    | defn n us type val _ _ := do
      n ← n.get_suffix,
      lemma_name ← to_string <$> pp format!"{n}_{field}",
      assert_not_declared lemma_name,
      handle_defn lemma_name conf e n us type val field
    | _ := interaction_monad.fail format!"\"{obj_def}\" must be a definition, not a lemma, theorem, or axiom!"
    end
  end

end rfl_lemma

meta def rfl_lemma_core (conf : rfl_lemma.config) : lean.parser unit := do
  obj_def ← ident,
  field ← ident,
  lean.parser.of_tactic_safe (rfl_lemma.handle conf obj_def field) >>= emit_code_here

@[user_command]
meta def rfl_lemma_cmd (d : decl_meta_info) (_ : parse $ tk "rfl_lemma") : lean.parser unit :=
  rfl_lemma_core {}

@[user_command]
meta def rfl_lemma_private_cmd (d : decl_meta_info) (_ : parse $ tk "private rfl_lemma") : lean.parser unit :=
  rfl_lemma_core {priv := tt}

@[user_command]
meta def rfl_lemma_question_cmd (d : decl_meta_info) (_ : parse $ tk "rfl_lemma?") : lean.parser unit :=
  rfl_lemma_core {trace := tt}

@[user_command]
meta def rfl_lemma_question_private_cmd (d : decl_meta_info) (_ : parse $ tk "private rfl_lemma?") : lean.parser unit :=
  rfl_lemma_core {trace := tt, priv := tt}

end tidy.command