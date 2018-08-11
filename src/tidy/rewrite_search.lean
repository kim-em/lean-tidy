import .rewrite_search.engine
import .rewrite_search.strategy.edit_distance

open tidy.rewrite_search tidy.rewrite_search.strategy
open interactive interactive.types expr tactic

meta def do_rewrite_search (rs : list (expr × bool)) (cfg : config := {}) : tactic string := do
  t ← target,
  match t with
  | `(%%lhs = %%rhs) := do
    -- if cfg.trace_rules then
    --   do rs_strings ← pp_rules rs,
    --     trace ("rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
    -- else skip,
    -- (steps, r1, r2) ← rewrite_search rs cfg lhs rhs,
    -- if cfg.trace then trace "rewrite_search found proof:" else skip,
    -- prf2 ← mk_eq_symm r2.proof,
    -- prf ← mk_eq_trans r1.proof prf2,
    -- -- if cfg.trace then trace prf else skip,
    -- rs_strings ← pp_rules rs,
    -- explanation ← (do 
    --   needs_refl ← check_if_simple_rewrite_succeeds rs (r1, r2),
    --   return (explain_proof_concisely rs_strings (r1, r2) needs_refl)) <|> return (explain_proof rs_strings (r1, r2)),
    -- if cfg.trace_result then trace explanation          
    -- else skip,
    -- if cfg.trace_summary then 
    --   do name ← decl_name,
    --     trace format!"during elaboration of {name}, rewrite_search considered {steps} expressions, and found a chain of {r1.rewrites.length + r2.rewrites.length} rewrites"
    -- else skip,
    -- exact prf,
    -- return explanation,

    let strat := edit_distance_strategy,
    i ← mk_search_instance cfg rs strat lhs rhs,
    result ← i.search_until_abort,
    match result with
      | search_result.success str    := return str
      | search_result.failure reason := fail reason
    end
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

meta def rewrite_search_using (a : name) (cfg : config := {}) : tactic string :=
do names ← attribute.get_instances a,
  exprs ← names.mmap $ mk_const,
  hyps ← local_context,
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