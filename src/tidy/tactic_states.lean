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

meta def monadic_failed {σ α : Type} : interaction_monad σ α := interaction_monad.failed
meta def monadic_fail {σ : Type} {α : Type u} {β : Type v} [has_to_format β] (msg : β) : interaction_monad σ α :=
interaction_monad.fail msg

meta instance interaction_monad.alternative (σ : Type): alternative (interaction_monad σ) := {
  @interaction_monad.monad σ with
  orelse := λ { α : Type } (t₁ t₂ : interaction_monad σ α) s, 
              match (t₁ s) with
              | result.success   a       s' := result.success a s'
              | result.exception msg pos s' := (t₂ s')
              end,
  failure := λ { α : Type }, monadic_failed,
}

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

meta def pack_states {σ τ ρ α : Type}: interaction_monad ((σ × τ) × ρ) α → interaction_monad (σ × (τ × ρ)) α :=
λ t s, (t ((s.1, s.2.1), s.2.2)).map(λ s', (s'.1.1, (s'.1.2, s'.2)))

meta def unpack_states {σ τ ρ α : Type}: interaction_monad (σ × (τ × ρ)) α → interaction_monad ((σ × τ) × ρ) α :=
λ t s, (t (s.1.1, (s.1.2, s.2))).map(λ s', ((s'.1, s'.2.1), s'.2.2))

-- TODO define coercions for unpack_states, and possibly for pack_states too?

meta instance tactic_lift_product ( τ τ' : Type ) [tactic_lift τ] [tactic_lift τ'] : tactic_lift (τ × τ') := {
  lift := λ { σ α } [uts : underlying_tactic_state σ] t, pack_states (@tactic_lift.lift τ' _ _ _ (@product_underlying_tactic_state _ _ uts) (@tactic_lift.lift τ _ _ _ uts t))
}

meta instance tactic_lift_coe (τ : Type) [tactic_lift τ] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad (σ × τ) α) :=
⟨ tactic_lift.lift τ ⟩

-- Lean won't chain two coercions together for us, so we provide a shortcut here.
meta instance tactic_lift_twice_coe (τ τ' : Type) [tactic_lift τ] [tactic_lift τ'] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad ((σ × τ) × τ') α) :=
⟨ λ t, tactic_lift.lift τ' (tactic_lift.lift τ t) ⟩

meta instance : tactic_lift unit := {
  lift := λ { σ α : Type } [underlying_tactic_state σ] ( t : interaction_monad σ α ),
            λ s, (t s.1).map(λ s, (s, unit.star))
}

meta instance discard_unit_coe (σ α : Type) : has_coe (interaction_monad (σ × unit) α) (interaction_monad σ α) := {
  coe := λ t s, (t (s, unit.star)).map(λ s', s'.1)
}

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

