-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

universe variables u

private meta structure chain_progress (α : Type) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (tactic α) )

variables {α : Type}

private meta def chain_core' (tactics : list (tactic α)) 
    : chain_progress α → tactic (list α × bool)
| ⟨ 0     , results, _       ⟩ := pure (results, ff) -- we've exceeded max_steps
| ⟨ _     , results, []      ⟩ := pure (results, tt)
| ⟨ n+1, results, t :: ts ⟩ := (done >> (pure (results, tt))) <|>
                                  (t >>= (λ result, (chain_core' ⟨ n, result :: results, tactics ⟩ ))) <|>
                                  (chain_core' ⟨ n+1, results, ts ⟩)

structure chain_cfg := 
  ( max_steps          : nat  := 500 )
  ( fail_on_max_steps  : bool := ff )
  ( trace_steps        : bool := ff )

meta def chain_core (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
do
  (results, completed) ← chain_core' tactics ⟨ cfg.max_steps, [], tactics ⟩,
  guard completed <|> (do name ← decl_name,
                          let msg := format!"chain iteration limit exceeded during elaboration of {name}",
                          if cfg.fail_on_max_steps then
                            fail msg
                          else 
                            trace msg),
  pure results

variable [has_to_format α]

meta def trace_output (t : tactic α) : tactic α :=
do r ← t,
   name ← decl_name,
   trace format!"chain successfully applied a tactic during elaboration of {name} with result: {r}",
   pure r

private meta def chain_handle_trace (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
if cfg.trace_steps then
  chain_core cfg (tactics.map trace_output)
else 
  chain_core cfg tactics

meta def chain (cfg : chain_cfg) (tactics : list (tactic α)) : tactic (list α) :=
do sequence ← chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> fail "chain tactic made no progress",
   pure sequence.reverse
