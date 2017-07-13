import .if_then_else
import .tactic_states

private meta structure chain_progress ( σ α : Type ) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (interaction_monad σ α) )

open nat tactic

private meta def chain' { σ α : Type } [ tactic_lift σ ] ( tactics : list (interaction_monad σ α) ) 
    : chain_progress σ α → interaction_monad σ (list α)
| ⟨ 0     , _      , _       ⟩ := fail "chain iteration limit exceeded"
| ⟨ _     , results, []      ⟩ := pure results
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                   (pure results)
                                   (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
)

universe variables u

meta def monadic_repeat_at_most_core { σ : Type } { α : Type u } ( t : interaction_monad σ α ) : nat → (list α) → interaction_monad σ (list α)
| 0        results := pure results
| (succ n) results := (do r ← t, monadic_repeat_at_most_core n (r :: results)) <|> pure results

meta def monadic_repeat_at_most { σ : Type } { α : Type u } ( limit : nat ) ( t : interaction_monad σ α ) : interaction_monad σ (list α) := monadic_repeat_at_most_core t limit []

/-- `first [t_1, ..., t_n]` applies the first tactic that doesn't fail.
   The tactic fails if all t_i's fail. -/
meta def monadic_first { σ : Type } { α : Type u } : list (interaction_monad σ α) → interaction_monad σ α
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> monadic_first ts
