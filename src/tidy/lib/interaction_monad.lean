universes u v
variable {state : Type}
variables {α : Type u} {β : Type v}
local notation `m` := interaction_monad state

meta def interaction_monad_orelse_intercept_safe {α : Type u} (t₁ : m α) (t₂ : option (unit → format) → option pos → m α) (fallback : α) : m α :=
let t₃ : m α := do return fallback in
λ s, interaction_monad.result.cases_on (t₁ s)
  interaction_monad.result.success
  (λ e₁ ref₁ s', interaction_monad.result.cases_on (t₂ e₁ ref₁ s)
    interaction_monad.result.success
    (λ e₂ ref₂ s'', interaction_monad.result.cases_on (t₃ s)
      interaction_monad.result.success
      interaction_monad.result.exception
    )
  )