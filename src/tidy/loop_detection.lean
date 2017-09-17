-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .tactic_states
import .hash_target

open tactic
open interaction_monad

universe variables u v

structure loop_detection_state :=
  ( allowed_collisions : nat )
  ( past_goals : list string )

meta def get_state_hash { σ : Type } [ underlying_tactic_state σ ] ( s : σ ) : string :=
  match (hash_target s) with
  | result.success   hash    s' := hash
  | result.exception pos msg s' := undefined_core "unreachable"
  end

meta def detect_looping
  { σ α : Type }
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × loop_detection_state) α )
  ( allowed_collisions : nat := 0 )
    : interaction_monad σ α :=
λ s, (t (s, ⟨ allowed_collisions, [ get_state_hash s ] ⟩ )).map(λ s'', s''.1)

private meta def lift_ignore_first { σ τ α : Type } ( t : interaction_monad τ α ) : interaction_monad (σ × τ) α :=
  λ s, match t s.2 with
       | result.success   a       s2' := result.success   a       (s.1, s2')
       | result.exception msg pos s2' := result.exception msg pos (s.1, s2')
       end

private meta def lift_ignore_second { σ τ α : Type } ( t : interaction_monad σ α ) : interaction_monad (σ × τ) α :=
  λ s, match t s.1 with
       | result.success   a       s1' := result.success   a       (s1', s.2)
       | result.exception msg pos s1' := result.exception msg pos (s1', s.2)
       end

meta def loop_detector (hash : string) : interaction_monad loop_detection_state unit :=
λ s, if s.past_goals.mem hash then
       if s.allowed_collisions > 0 then
         result.success () ⟨ s.allowed_collisions - 1, s.past_goals ⟩
       else
         interaction_monad.fail ("detected looping" /-++ "\n" ++ s.2.past_goals.to_string ++ "\n" ++ hash-/) s
     else
       result.success () ⟨ s.allowed_collisions, hash :: s.past_goals ⟩

@[inline] private meta def read' { σ : Type } : interaction_monad σ σ :=
λ s, result.success s s

meta def instrument_for_loop_detection { σ α : Type } [uts : underlying_tactic_state σ] ( t : interaction_monad σ α ) : interaction_monad (σ × loop_detection_state) α :=
  do a ← lift_ignore_second t,
     s ← read',
     let hash := get_state_hash s,
     lift_ignore_first (loop_detector hash),
     pure a

meta instance instrument_for_loop_detection_coercion { σ α : Type } [uts : underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad (σ × loop_detection_state) α) :=
⟨ instrument_for_loop_detection ⟩ 

-- meta instance lift_to_loop_detection_tactic : tactic_lift loop_detection_state :=
-- ⟨ λ { σ α : Type } [uts : underlying_tactic_state σ], @instrument_for_loop_detection σ α uts ⟩

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