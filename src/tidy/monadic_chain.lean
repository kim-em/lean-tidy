import .if_then_else
import .tactic_states

private meta structure chain_progress ( σ α : Type ) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (interaction_monad (tactic_state × σ) α) )

open nat tactic

private meta def chain' { σ α : Type } [ tactic_lift σ ] ( tactics : list (interaction_monad (tactic_state × σ) α) ) 
    : chain_progress σ α → interaction_monad (tactic_state × σ) (list α)
| ⟨ 0     , _      , _       ⟩ := fail "chain iteration limit exceeded"
| ⟨ _     , results, []      ⟩ := pure results
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                   (pure results)
                                   (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
)
