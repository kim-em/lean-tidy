-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

-- This is a fancy version of chain.lean, but it's not particularly useful.

import .if_then_else
import .tactic_states
import .loop_detection
import .recover
import .timing

open nat tactic

universe variables u

private meta structure chain_progress ( σ α : Type ) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (interaction_monad (tactic_state × σ) α) )
  ( timing_data       : list (ℕ × ℕ) )
 
private def update_timing_data (success : bool) (time : ℕ) (index : ℕ) (timing_data : list (ℕ × ℕ)) : list (ℕ × ℕ) :=
let t := (timing_data.nth index).get_or_else (0, 0) in
timing_data.update_nth index (if success then (t.1 + time, t.2) else (t.1, t.2 + time))

private meta def monadic_chain_core' { σ α : Type } ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : chain_progress σ α → interaction_monad (tactic_state × σ) (list α × bool × list (ℕ × ℕ))
| ⟨ 0     , results, _      , timing ⟩ := pure (results, ff, timing) -- we've exceeded max_steps
| ⟨ _     , results, []     , timing ⟩ := pure (results, tt, timing)
| ⟨ succ n, results, t :: ts, timing ⟩ := if_then_else interaction_monad.done
                                          (pure (results, tt, timing))
                                          (let time_before := systemtime in
                                          (dependent_if_then_else t 
                                              (λ result, (monadic_chain_core' ⟨ n, result :: results, tactics, update_timing_data tt (systemtime - time_before) ts.length timing ⟩ ))
                                              (monadic_chain_core' ⟨ succ n, results, ts, update_timing_data ff (systemtime - time_before) ts.length timing ⟩))
)

structure chain_cfg := 
  ( max_steps          : nat  := 500 )
  ( fail_on_max_steps  : bool := ff )
  ( trace_steps        : bool := ff )
  ( allowed_collisions : nat  := 0 )
  ( fail_on_loop       : bool := ff ) -- be careful this is very slow, because it pretty prints states to compare
  ( trace_timing       : bool := ff )


meta def monadic_chain_core { σ α : Type } ( cfg : chain_cfg ) ( tactics : list (interaction_monad (tactic_state × σ) α) ) : interaction_monad (tactic_state × σ) (list α) :=
do
  (results, completed, timing) ← monadic_chain_core' tactics ⟨ cfg.max_steps, [], tactics, list.repeat (0, 0) tactics.length ⟩,
  if cfg.trace_timing then
    do name ← id_lift decl_name,
       let msg := format!"tactic invocation times during elaboration of {name} (success/failure): {timing.reverse}",
       interaction_monad.trace msg
  else
    result.success (),
  guard completed <|> (do name ← id_lift decl_name,
                          let msg := format!"chain iteration limit exceeded during elaboration of {name}",
                          if cfg.fail_on_max_steps then
                            interaction_monad.fail msg
                          else 
                            interaction_monad.trace msg),
  pure results

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

meta def trace_output { σ α : Type } [ has_to_format α ] ( t : interaction_monad (tactic_state × σ) α ) : interaction_monad (tactic_state × σ) α :=
do r ← t,
   name ← id_lift decl_name,
   interaction_monad.trace format!"chain succeeded during elaboration of {name} with result: {r}",
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

