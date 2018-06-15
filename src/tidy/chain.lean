-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .if_then_else
import .recover

open nat tactic

universe variables u

private meta structure chain_progress ( α : Type ) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (tactic α) )
 
private meta def chain_core' { α : Type } ( tactics : list (tactic α) ) 
    : chain_progress α → tactic (list α × bool)
| ⟨ 0     , results, _       ⟩ := pure (results, ff) -- we've exceeded max_steps
| ⟨ _     , results, []      ⟩ := pure (results, tt)
| ⟨ succ n, results, t :: ts ⟩ := if_then_else tactic.done
                                          (pure (results, tt))
                                          (dependent_if_then_else t 
                                              (λ result, (chain_core' ⟨ n, result :: results, tactics ⟩ ))
                                              (chain_core' ⟨ succ n, results, ts ⟩)
)

structure chain_cfg := 
  ( max_steps          : nat  := 500 )
  ( fail_on_max_steps  : bool := ff )
  ( trace_steps        : bool := ff )

meta def chain_core { α : Type } ( cfg : chain_cfg ) ( tactics : list (tactic α) ) : tactic (list α) :=
do
  (results, completed) ← chain_core' tactics ⟨ cfg.max_steps, [], tactics ⟩,
  guard completed <|> (do name ← decl_name,
                          let msg := format!"chain iteration limit exceeded during elaboration of {name}",
                          if cfg.fail_on_max_steps then
                            fail msg
                          else 
                            trace msg),
  pure results

meta def trace_output { α : Type } [ has_to_format α ] ( t : tactic α ) : tactic α :=
do r ← t,
   name ← decl_name,
   trace format!"chain succeeded during elaboration of {name} with result: {r}",
   pure r

private meta def chain_handle_trace
  { α : Type } [ has_to_format α ] 
  ( cfg : chain_cfg ) 
  ( tactics : list (tactic α) ) 
    : tactic (list α) :=
if cfg.trace_steps then
  chain_core cfg (tactics.map trace_output)
else 
  chain_core cfg tactics

meta def chain
  { α : Type } [ has_to_format α ] 
  ( tactics : list (tactic α) ) 
  ( cfg : chain_cfg := {} ) 
    : tactic (list α) :=
do sequence ← chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> fail "chain tactic made no progress",
   pure sequence.reverse
