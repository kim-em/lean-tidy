-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

universe variables u v w

meta class underlying_tactic_state ( σ : Type ) :=
  ( to_tactic_state : σ → tactic_state )

meta instance underlying_tactic_state_coe (σ : Type) [underlying_tactic_state σ] : has_coe σ tactic_state :=
⟨ underlying_tactic_state.to_tactic_state ⟩

meta instance trivial_underlying_tactic_state : underlying_tactic_state tactic_state :=
{ to_tactic_state := id }

meta instance product_underlying_tactic_state ( σ τ : Type ) [underlying_tactic_state σ]: underlying_tactic_state (σ × τ) :=
{ to_tactic_state := λ p, underlying_tactic_state.to_tactic_state p.1 }

meta class tactic_lift ( τ : Type ) :=
  ( lift : Π { σ α : Type } [underlying_tactic_state σ], interaction_monad σ α → interaction_monad (σ × τ) α )

meta instance tactic_lift_coe (τ : Type) [tactic_lift τ] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad (σ × τ) α) :=
⟨ tactic_lift.lift τ ⟩

meta instance interaction_monad.has_orelse (σ : Type) : has_orelse (interaction_monad σ) := {
  orelse := λ { α : Type u } (t₁ t₂ : interaction_monad σ α) s, 
              match (t₁ s) with
              | result.success   a       s' := result.success a s'
              | result.exception msg pos s' := match (t₂ s') with
                                               | result.success   a'        s'' := result.success   a'        s''
                                               | result.exception msg' pos' s'' := result.exception msg' pos' s''
                                               end
              end
}

meta def failed {σ α : Type} : interaction_monad σ α := interaction_monad.failed
meta def fail {σ : Type} {α : Type u} {β : Type v} [has_to_format β] (msg : β) : interaction_monad σ α :=
interaction_monad.fail msg
