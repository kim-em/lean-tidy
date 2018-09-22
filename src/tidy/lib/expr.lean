import data.list

import .string
import .pretty_print

meta def binder_info.brackets : binder_info → string × string
| binder_info.default  := ("(", ")")
| binder_info.implicit := ("{", "}")
| binder_info.inst_implicit := ("[", "]")
| bi := ("?", "?" ++ repr bi)

namespace expr

private meta def unroll_pi_params_aux : list (name × expr × binder_info) → expr → list (name × expr × binder_info) × expr
| curr (expr.pi var_n bi var_type rest) :=
  unroll_pi_params_aux (curr.concat (var_n, var_type, bi)) rest
| curr ex := (curr, ex)

meta def unroll_pi_params : expr → list (name × expr × binder_info) × expr :=
  unroll_pi_params_aux []

private meta def unroll_lam_params_aux : list (name × expr × binder_info) → expr → list (name × expr × binder_info) × expr
| curr (expr.lam var_n bi var_type rest) :=
  unroll_lam_params_aux (curr.concat (var_n, var_type, bi)) rest
| curr ex := (curr, ex)

meta def unroll_lam_params : expr → list (name × expr × binder_info) × expr :=
  unroll_lam_params_aux []

end expr

namespace param

meta def to_name : name × expr × binder_info → name
| (n, _, _) := n

meta def to_type : name × expr × binder_info → expr
| (_, e, _) := e

meta def to_binder_info : name × expr × binder_info → binder_info
| (_, _, bi) := bi

meta def set_name : name × expr × binder_info → name → name × expr × binder_info
| (_, e, bi) n := (n, e, bi)

meta def set_type : name × expr × binder_info → expr → name × expr × binder_info
| (n, _, bi) e := (n, e, bi)

meta def set_binder_info : name × expr × binder_info → binder_info → name × expr × binder_info
| (n, e, _) bi := (n, e, bi)

meta def pretty_print : name × expr × binder_info → tactic string
| (n, e, bi) := let brackets := bi.brackets in do
  ppe ← _root_.pretty_print e,
  return $ brackets.1 ++ n.to_string ++ " : " ++ ppe ++ brackets.2

private meta def instantiate_list_aux : list (name × expr × binder_info) → list (name × expr × binder_info) → list (name × expr × binder_info)
| seen [] := seen
| seen ((n, e, bi) :: rest) :=
  let e := e.instantiate_vars $ seen.reverse.map $ λ v, expr.const v.1 [] in
  instantiate_list_aux (seen.concat (n, e, bi)) rest

meta def instantiate_list : list (name × expr × binder_info) → list (name × expr × binder_info) :=
  instantiate_list_aux []

meta def instantiate (e : expr) (l : list (name × expr × binder_info)) : expr :=
  e.instantiate_vars $ l.reverse.map $ λ v : (name × expr × binder_info), expr.const v.1 []

meta def drop_implicit : name × expr × binder_info → option (name × expr × binder_info)
| (n, e, binder_info.default) := some (n, e, binder_info.default)
| (_, _, _) := none

meta def list_to_args (l : list (name × expr × binder_info)) (drop_impl : bool := tt) : tactic string := do
  l ← (instantiate_list l).mmap param.pretty_print,
  return $ string.lconcat $ l.intersperse " "

meta def list_to_invocation (l : list (name × expr × binder_info)) (drop_impl : bool := tt) : string :=
  let l := if drop_impl then l.filter_map drop_implicit else l in
  string.lconcat $ ((instantiate_list l).map $ to_string ∘ to_name).intersperse " "

end param

namespace app

meta def count : expr → ℕ
| (expr.app e _) := 1 + count e
| _              := 0

meta def pop_n : expr → ℕ → expr
| e 0 := e
| (expr.app e _) n := pop_n e (n - 1)
| e _ := e

meta def pop (e : expr) : expr := pop_n e 1

meta def get_arg : expr → option expr
| (expr.app _ f) := some f
| _              := none

meta def chop : expr → option (name × list level × list expr)
| (expr.const n us) := some (n, us, [])
| (expr.app e v) :=
  match chop e with
  | none   := none
  | some (n, us, vs) := some (n, us, (v :: vs))
  end
| _ := none

end app

namespace structure_instance

meta def extract_nth_field (st : expr) (n : ℕ) : option expr :=
  app.get_arg $ app.pop_n st ((app.count st) - (n + 1))

meta def extract_field (st : expr) (pi : environment.projection_info) : option expr :=
  extract_nth_field st (pi.nparams + pi.idx)

end structure_instance