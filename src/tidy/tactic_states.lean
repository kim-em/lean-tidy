-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

universe variables u v w

-- TODO surely this should be in the standard library
meta definition interaction_monad.result.map { α σ σ' : Type } (r : interaction_monad.result σ α) (f : σ → σ') : interaction_monad.result σ' α :=
match r with 
| result.success   a       s := result.success   a       (f s)
| result.exception msg pos s := result.exception msg pos (f s)
end

meta instance interaction_monad.alternative (σ : Type): alternative (interaction_monad (tactic_state × σ)) := {
  @interaction_monad.monad (tactic_state × σ) with
  orelse := λ { α : Type } (t₁ t₂ : interaction_monad (tactic_state × σ) α) s, 
              match (t₁ s) with
              | result.success   a       s' := result.success a s'
              | result.exception msg pos s' := (t₂ (s.1, s'.2))    -- we discard the tactic_state from the failed branch, but keep the other state
              end,
  failure := λ { α : Type }, interaction_monad.failed,
}

meta class underlying_tactic_state ( σ : Type ) :=
  ( to_tactic_state : σ → tactic_state )

meta instance underlying_tactic_state_coe (σ : Type) [underlying_tactic_state σ] : has_coe σ tactic_state :=
⟨ underlying_tactic_state.to_tactic_state ⟩

meta instance trivial_underlying_tactic_state : underlying_tactic_state tactic_state :=
{ to_tactic_state := id }

meta instance product_underlying_tactic_state ( σ τ : Type ) [underlying_tactic_state σ]: underlying_tactic_state (σ × τ) :=
{ to_tactic_state := λ p, underlying_tactic_state.to_tactic_state p.1 }

meta def pack_states {σ τ ρ α : Type}: interaction_monad ((σ × τ) × ρ) α → interaction_monad (σ × (τ × ρ)) α :=
λ t s, (t ((s.1, s.2.1), s.2.2)).map(λ s', (s'.1.1, (s'.1.2, s'.2)))

meta def unpack_states {σ τ ρ α : Type}: interaction_monad (σ × (τ × ρ)) α → interaction_monad ((σ × τ) × ρ) α :=
λ t s, (t (s.1.1, (s.1.2, s.2))).map(λ s', ((s'.1, s'.2.1), s'.2.2))

meta def unit_lift { α : Type } ( t : tactic α ) : interaction_monad (tactic_state × unit) α := λ s, (t s.1).map(λ s, (s, unit.star))
meta def id_lift {σ α : Type} ( t : tactic α ) : interaction_monad (tactic_state × σ) α := λ s, (t s.1).map(λ y, (y, s.2))

meta instance discard_unit_coe (σ α : Type) : has_coe (interaction_monad (σ × unit) α) (interaction_monad σ α) := {
  coe := λ t s, (t (s, unit.star)).map(λ s', s'.1)
}