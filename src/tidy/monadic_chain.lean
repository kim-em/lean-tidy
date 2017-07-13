-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .if_then_else
import .tactic_states
import .loop_detection

open nat tactic

universe variables u

meta def interaction_monad.done {σ : Type} [underlying_tactic_state σ] : interaction_monad σ unit :=
λ s, (tactic.done (underlying_tactic_state.to_tactic_state s)).map(λ s', s)

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

-- meta def monadic_repeat_at_most_core { σ : Type } { α : Type u } ( t : interaction_monad σ α ) : nat → (list α) → interaction_monad σ (list α)
-- | 0        results := pure results
-- | (succ n) results := (do r ← t, monadic_repeat_at_most_core n (r :: results)) <|> pure results

-- meta def monadic_repeat_at_most { σ : Type } { α : Type u } ( limit : nat ) ( t : interaction_monad σ α ) : interaction_monad σ (list α) := monadic_repeat_at_most_core t limit []

-- /-- `first [t_1, ..., t_n]` applies the first tactic that doesn't fail.
--    The tactic fails if all t_i's fail. -/
-- meta def monadic_first { σ : Type } { α : Type u } : list (interaction_monad σ α) → interaction_monad σ α
-- | []      := monadic_fail "first tactic failed, no more alternatives"
-- | (t::ts) := t <|> monadic_first ts

structure chain_cfg := 
  ( max_steps          : nat  := 500 )
  ( trace_steps        : bool := ff )
  ( allowed_collisions : nat  := 0 )
  ( fail_on_loop       : bool := tt )
  
meta def monadic_chain_core { σ α : Type } [ tactic_lift σ ] ( cfg : chain_cfg ) ( tactics : list (interaction_monad (tactic_state × σ) α) ) : interaction_monad (tactic_state × σ) (list α) :=
monadic_chain_core' tactics ⟨ cfg.max_steps, [], tactics ⟩

private meta def monadic_chain_handle_looping
  { σ α : Type } [ tactic_lift σ ] [ has_to_format α ] 
  ( cfg : chain_cfg ) 
  ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : interaction_monad (tactic_state × σ) (list α) :=
if cfg.fail_on_loop then
  let instrumented_tactics := tactics.map(λ t, pack_states (instrument_for_loop_detection t)) in
  detect_looping (unpack_states (monadic_chain_core cfg instrumented_tactics)) cfg.allowed_collisions
else
  monadic_chain_core cfg tactics

meta def trace_output { σ α : Type } [ tactic_lift σ ] [ has_to_format α ] ( t : interaction_monad (tactic_state × σ ) α ) : interaction_monad (tactic_state × σ ) α :=
do r ← t,
   trace format!"succeeded with result: {r}",
   pure r

private meta def monadic_chain_handle_trace
  { σ α : Type } [ tactic_lift σ ] [ has_to_format α ] 
  ( cfg : chain_cfg ) 
  ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : interaction_monad (tactic_state × σ) (list α) :=
if cfg.trace_steps then
  monadic_chain_handle_looping cfg (tactics.map trace_output)
else 
  monadic_chain_handle_looping cfg tactics

meta def monadic_chain
  { σ α : Type } [ tactic_lift σ ] [ has_to_format α ] 
  ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
  ( cfg : chain_cfg := {} ) 
    : interaction_monad (tactic_state × σ) (list α) :=
do sequence ← monadic_chain_handle_trace cfg tactics,
   guard (sequence.length > 0) <|> fail "chain tactic made no progress",
   pure sequence.reverse

meta def chain
  { α : Type } [ has_to_format α ] 
  ( tactics : list (tactic α) ) 
  ( cfg : chain_cfg := {} ) 
    : tactic (list α) :=
@monadic_chain unit _ _ _ (tactics.map(λ t, t)) cfg

def chain_test_simp_succeeded : 1 = 1 :=
begin
  chain [ interactive_simp ]
end

def chain_test_without_loop_detection_skip_does_nothing : 1 = 1 :=
begin
  success_if_fail { chain [ skip ] { fail_on_loop := ff } }, -- fails because 'chain iteration limit exceeded'
  refl
end

def chain_test_without_loop_detection_skip_does_nothing' : 1 = 1 :=
begin
  success_if_fail { chain [ skip, interactive_simp ] { fail_on_loop := ff } }, -- fails because 'chain iteration limit exceeded'
  refl
end

def chain_test_loop_detection : 1 = 1 :=
begin
  chain [ skip, interactive_simp ] {}
end

def chain_test_loop_detection' : 1 = 1 :=
begin
  chain [ skip, interactive_simp ] { allowed_collisions := 5, trace_steps := tt }
end