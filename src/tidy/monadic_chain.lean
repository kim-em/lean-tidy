-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .if_then_else
import .tactic_states
import .loop_detection
import .recover

open nat tactic

universe variables u

meta def interaction_monad.done {σ : Type} [underlying_tactic_state σ] : interaction_monad σ unit :=
λ s, (done_no_metavariables (underlying_tactic_state.to_tactic_state s)).map(λ s', s)

private meta structure chain_progress ( σ α : Type ) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (interaction_monad (tactic_state × σ) α) )
 
private meta def monadic_chain_core' { σ α : Type } ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : chain_progress σ α → interaction_monad (tactic_state × σ) (list α)
| ⟨ 0     , _      , _       ⟩ := interaction_monad.fail "chain iteration limit exceeded"
| ⟨ _     , results, []      ⟩ := pure results
| ⟨ succ n, results, t :: ts ⟩ := if_then_else interaction_monad.done
                                   (pure results)
                                   (dependent_if_then_else t 
                                      (λ result, (monadic_chain_core' ⟨ n, result :: results, tactics ⟩ ))
                                      (monadic_chain_core' ⟨ succ n, results, ts ⟩)
)

structure chain_cfg := 
  ( max_steps          : nat  := 500 )
  ( trace_steps        : bool := ff )
  ( allowed_collisions : nat  := 0 )
  ( fail_on_loop       : bool := tt )
  
meta def monadic_chain_core { σ α : Type } ( cfg : chain_cfg ) ( tactics : list (interaction_monad (tactic_state × σ) α) ) : interaction_monad (tactic_state × σ) (list α) :=
monadic_chain_core' tactics ⟨ cfg.max_steps, [], tactics ⟩

private meta def monadic_chain_handle_looping
  { σ α : Type } [ has_to_format α ] 
  ( cfg : chain_cfg ) 
  ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : interaction_monad (tactic_state × σ) (list α) :=
if cfg.fail_on_loop then
  let instrumented_tactics := tactics.map(λ t, pack_states (instrument_for_loop_detection t)) in
  detect_looping (unpack_states (monadic_chain_core cfg instrumented_tactics)) cfg.allowed_collisions
else
  monadic_chain_core cfg tactics

meta def interaction_monad.trace {σ : Type} [underlying_tactic_state σ] {α : Type u} [has_to_tactic_format α] (a : α) : interaction_monad σ unit :=
λ s, (trace a (underlying_tactic_state.to_tactic_state s)).map(λ s', s)

meta def trace_output { σ α : Type } [ has_to_format α ] ( t : interaction_monad (tactic_state × σ) α ) : interaction_monad (tactic_state × σ) α :=
do r ← t,
   interaction_monad.trace format!"succeeded with result: {r}",
   pure r

private meta def monadic_chain_handle_trace
  { σ α : Type } [ has_to_format α ] 
  ( cfg : chain_cfg ) 
  ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : interaction_monad (tactic_state × σ) (list α) :=
if cfg.trace_steps then
  monadic_chain_handle_looping cfg (tactics.map trace_output)
else 
  monadic_chain_handle_looping cfg tactics

meta def monadic_chain
  { σ α : Type } [ has_to_format α ] 
  ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
  ( cfg : chain_cfg := {} ) 
    : interaction_monad (tactic_state × σ) (list α) :=
do sequence ← monadic_chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> interaction_monad.fail "chain tactic made no progress",
   pure sequence.reverse

meta def chain
  { α : Type } [ has_to_format α ] 
  ( tactics : list (tactic α) ) 
  ( cfg : chain_cfg := {} ) 
    : tactic (list α) :=
@monadic_chain unit _ _ (tactics.map(λ t, unit_lift t)) cfg

