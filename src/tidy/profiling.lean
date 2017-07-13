-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .tactic_states
import .if_then_else

open tactic

universe variables u v

structure invocation_count := 
  ( invocations : ℕ )

meta def exception_in_messages {α : Sort u} : α := undefined_core "exception in profiling messages!"

meta def profiling
  { σ α : Type } 
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × invocation_count) α ) 
  ( success_handler   : invocation_count → tactic unit := λ p, trace format!"success, with {p.invocations} invocations" ) 
  ( exception_handler : invocation_count → tactic unit := λ p, trace format!"failed, with {p.invocations} invocations" ) 
    : interaction_monad σ (α × invocation_count) :=
λ s, match t (s, ⟨ 0 ⟩) with
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

meta instance lift_to_profiling_tactic : tactic_lift invocation_count := 
{
  lift := λ { σ α : Type } [underlying_tactic_state σ] ( t : interaction_monad σ α ) (s : σ × invocation_count),
            (t s.1).map(λ ts, (ts, ⟨ s.2.invocations + 1 ⟩ ))
} 

lemma profile_test : true :=
begin
profiling $ skip >> skip,             -- 2
profiling $ skip >> skip >> skip,     -- 3
success_if_fail { profiling $ done }, -- 1

profiling $ skip <|> done,            -- 1
profiling $ done <|> skip,            -- 2

profiling $ (skip <|> done) >> skip,  -- 2

profiling $ done <|> done <|> skip,   -- 3

success_if_fail { profiling $ done <|> done }, -- 2

triv
end
