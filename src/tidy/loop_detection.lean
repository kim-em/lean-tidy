-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .tactic_states
import .hash_target

open tactic

universe variables u v

structure loop_detection_state := 
  ( allowed_collisions : nat )
  ( past_goals : list string )

meta def unreachable {α : Sort u} : α := undefined_core "unreachable"

meta def detect_looping
  { σ α : Type } 
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × loop_detection_state) α ) 
  ( allowed_collisions : nat := 0 )
    : interaction_monad σ α :=
λ s, match (hash_target s) with
     | result.success   hash    s' := (t (s, ⟨ allowed_collisions, [ hash ] ⟩ )).map(λ s'', s''.1)
     | result.exception pos msg s' := unreachable
     end

meta def instrument_for_loop_detection { σ α : Type } [uts : underlying_tactic_state σ] ( t : interaction_monad σ α ) : interaction_monad (σ × loop_detection_state) α :=
λ (s : σ × loop_detection_state),
            match t s.1 with
            | result.success   a       s' := match (hash_target (@underlying_tactic_state.to_tactic_state _ uts s')) with -- FIXME why doesn't the coercion work? why can't Lean find uts itself?
                                             | result.success hash s'' := if s.2.past_goals.mem hash then
                                                                            if s.2.allowed_collisions > 0 then
                                                                              result.success a (s', ⟨ s.2.allowed_collisions - 1, s.2.past_goals ⟩ )
                                                                            else 
                                                                              match (@tactic.fail α string _ ("detected looping" /-++ "\n" ++ s.2.past_goals.to_string ++ "\n" ++ hash-/)) s'' with -- FIXME this duplicates code above
                                                                              | result.success   a       s''' := unreachable
                                                                              | result.exception pos msg s''' := result.exception pos msg (s', s.2)
                                                                              end
                                                                          else  
                                                                            result.success a (s', ⟨ s.2.allowed_collisions, hash :: s.2.past_goals ⟩ )
                                             | _ := unreachable
                                             end
            | result.exception msg pos s' := result.exception msg pos (s', s.2)
            end

meta instance lift_to_loop_detection_tactic : tactic_lift loop_detection_state := 
⟨ λ { σ α : Type } [uts : underlying_tactic_state σ], @instrument_for_loop_detection σ α uts ⟩ 

meta def interactive_simp := `[simp]

lemma looping_test_1 (a : empty): 1 = 1 :=
begin
success_if_fail { detect_looping $ skip },
success_if_fail { detect_looping $ skip >> skip },
refl
end
lemma looping_test_2 (a : empty): 1 = 1 :=
begin
detect_looping $ interactive_simp
end

