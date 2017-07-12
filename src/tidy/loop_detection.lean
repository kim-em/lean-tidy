-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .profiling

open tactic

universe variables u v


structure loop_detection_state := 
  ( past_goals : list string )

meta def unreachable {α : Sort u} : α := undefined_core "unreachable"

meta def detect_looping
  { σ α : Type } 
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × loop_detection_state) α ) 
    : interaction_monad σ α :=
λ s, match (hash_target s) with
     | result.success   hash    s' := match t (s, ⟨ [ hash ] ⟩ ) with
                                      | result.success a s''         := result.success a s''.1
                                      | result.exception pos msg s'' := result.exception pos msg (s''.1)
                                      end
     | result.exception pos msg s' := unreachable
     end

meta instance lift_to_loop_detection_tactic : tactic_lift loop_detection_state := 
{
  lift := λ { σ α : Type } [uts : underlying_tactic_state σ] ( t : interaction_monad σ α ) (s : σ × loop_detection_state),
            match t s.1 with
            | result.success   a       s' := match (hash_target (@underlying_tactic_state.to_tactic_state _ uts s')) with -- FIXME why doesn't the coercion work? why can't Lean find uts itself?
                                             | result.success hash s'' := if s.2.past_goals.mem hash then
                                                                            match (@tactic.fail α string _ ("detected looping\n" ++ s.2.past_goals.to_string ++ "\n" ++ hash)) s'' with -- FIXME this duplicates code above
                                                                            | result.success   a       s''' := unreachable
                                                                            | result.exception pos msg s''' := result.exception pos msg (s', s.2)
                                                                            end
                                                                          else  
                                                                            result.success a (s', ⟨ hash :: s.2.past_goals ⟩ )
                                             | _ := unreachable
                                             end
            | result.exception msg pos s' := result.exception msg pos (s', s.2)
            end
} 

meta def simp := `[simp]

lemma looping_test_1 (a : empty): 1 = 1 :=
begin
success_if_fail { detect_looping $ skip },
success_if_fail { detect_looping $ skip >> skip },
refl
end
lemma looping_test_2 (a : empty): 1 = 1 :=
begin
detect_looping $ simp
end

-- Lean won't chain two coercions together for us, so we provide a shortcut here.
meta instance tactic_lift_twice_coe (τ τ' : Type) [tactic_lift τ] [tactic_lift τ'] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad ((σ × τ) × τ') α) :=
⟨ λ t, tactic_lift.lift τ' (tactic_lift.lift τ t) ⟩

lemma looping_and_profiling_at_the_same_time_test_1 : true :=
begin
profiling $ (detect_looping $ triv),
end
lemma looping_and_profiling_at_the_same_time_test_2 : true :=
begin
success_if_fail { profiling $ detect_looping $ skip >> skip },
triv
end

