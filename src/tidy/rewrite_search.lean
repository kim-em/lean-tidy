import .rewrite_search.engine
import .rewrite_search.tracer.graph
import .rewrite_search.strategy.edit_distance

open tidy.rewrite_search tidy.rewrite_search.strategy
open interactive interactive.types expr tactic

meta def handle_search_result (cfg : config) (rules : list (expr × bool)) (result : search_result) : tactic string := do
match result with
| search_result.failure reason := fail reason
| search_result.success proof steps    := do
    if cfg.trace then trace "rewrite_search found proof:\n" ++ proof else skip,
    rules_strings ← pp_rules rules,
    explanation ← (do 
      needs_refl ← check_if_simple_rewrite_succeeds rules steps,
      return (explain_proof_concisely rules_strings steps needs_refl)) <|> return (explain_proof rules_strings steps),
    if cfg.trace_result then trace explanation          
    else skip,
    exact proof,
    return explanation,
end

meta def do_rewrite_search (rs : list (expr × bool)) (cfg : config := {}) : tactic string := do
  t ← target,
  match t with
  | `(%%lhs = %%rhs) := do
    -- if cfg.trace_rules then
    --   do rs_strings ← pp_rules rs,
    --     trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
    -- else skip,

    let strat := edit_distance_strategy,

    -- FIXME how to dynamically select these via a nicely-named argument? Typeclasses
    -- are getting in the way. Perhaps the best way is to fix universe issues which forced this
    result ← (
      if cfg.visualise then do
        i ← mk_search_instance cfg rs strat lhs rhs graph_tracer,
        i.search_until_abort
      else do
        i ← mk_search_instance cfg rs strat lhs rhs unit_tracer,
        i.search_until_abort
    ),

    handle_search_result result
  | _ := fail "target is not an equation"
  end

namespace tactic.interactive

meta def rewrite_search (rs: parse rw_rules) (cfg : config := {}) : tactic string := do
  rs ← rs.rules.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm)),
  do_rewrite_search rs cfg

meta def is_eq_after_binders : expr → bool
  | (expr.pi n bi d b) := is_eq_after_binders b
  | `(%%a = %%b)       := tt
  | _                  := ff

meta def load_exprs : list name → tactic (list expr)
| [] := return []
| (a :: rest) := do
  names ← attribute.get_instances a,
  u ← names.mmap $ mk_const,
  l ← load_exprs rest,
  return (u ++ l)

meta def rewrite_search_using (as : list name) (cfg : config := {}) : tactic string := do
  tgt ← target,
  if tgt.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,
  exprs ← load_exprs as,
  hyps ← local_context,
  hyps ← hyps.mfilter (λ h, (do t ← infer_type h, return ¬ t.has_meta_var)),
  let exprs := exprs ++ hyps,
  --  rules ← close_under_apps exprs, -- TODO don't do this for everything, it's too expensive: only for specially marked lemmas
  let rules := exprs,
  rules ← rules.mfilter $ λ r, (do t ← infer_type r, return (is_eq_after_binders t)),
  let pairs := rules.map (λ e, (e, ff)) ++ rules.map (λ e, (e, tt)),
  do_rewrite_search pairs cfg

end tactic.interactive

meta def search_attribute : user_attribute := {
  name := `search,
  descr := ""
}

run_cmd attribute.register `search_attribute

-- structure cat :=
--   (O : Type)
--   (H : O → O → Type)
--   (i : Π o : O, H o o)
--   (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
--   (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
--   (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
--   (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

-- attribute [search] cat.li cat.a

-- private example (C : cat) (X Y Z : C.O) (f : C.H X Y) (g : C.H Y X) (w : C.c g f = C.i Y) (h k : C.H Y Z) (p : C.c f h = C.c f k) : h = k := 
-- begin
-- rewrite_search_using `search {trace := tt, trace_rules:=tt},
-- end


-- PROJECT cache all_rewrites_list?
