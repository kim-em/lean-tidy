-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .tactic_states
import .if_then_else

open tactic

universe variables u v

meta def exception_in_messages {α : Sort u} : α := undefined_core "exception in profiling messages!"

structure invocation_count := 
  ( successful_invocations : ℕ )
  ( failed_invocations     : ℕ )

def invocation_count.record_success ( p : invocation_count ) : invocation_count :=
⟨ p.successful_invocations + 1, p.failed_invocations ⟩ 
def invocation_count.record_failure ( p : invocation_count ) : invocation_count :=
⟨ p.successful_invocations, p.failed_invocations + 1 ⟩ 

meta def profiling
  { σ α : Type } 
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × invocation_count) α ) 
  ( success_handler   : invocation_count → tactic unit := λ p, tactic.trace format!"success, with {p.successful_invocations} successful tactic invocations and {p.failed_invocations} failed tactic invocations" ) 
  ( exception_handler : invocation_count → tactic unit := λ p, tactic.trace format!"failed, with {p.successful_invocations} successful tactic invocations and {p.failed_invocations} failed tactic invocations" ) 
    : interaction_monad σ (α × invocation_count) :=
λ s, match t (s, ⟨ 0, 0 ⟩) with
     | result.success a ts         :=
         match success_handler ts.2 ts.1 with
         | result.success _ _             := result.success (a, ts.2) ts.1
         | result.exception msg' pos' ts' := exception_in_messages
         end        
     | result.exception msg pos ts := 
         match exception_handler ts.2 ts.1 with
         | result.success _ _             := result.exception msg pos ts.1
         | result.exception msg' pos' ts' := exception_in_messages
         end
     end 

meta def instrument_for_profiling { σ α : Type } [uts : underlying_tactic_state σ] ( t : interaction_monad σ α ) : interaction_monad (σ × invocation_count) α :=
 λ (s : σ × invocation_count),
            match (t s.1) with
            | result.success   a       s' := result.success   a       (s', s.2.record_success) 
            | result.exception msg pos s' := result.exception msg pos (s', s.2.record_failure)
            end


meta instance profiling_tactic_coercion { α : Type } : has_coe (interaction_monad tactic_state α) (interaction_monad (tactic_state × invocation_count) α) :=
⟨ instrument_for_profiling ⟩ 


