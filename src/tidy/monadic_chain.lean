import .if_then_else

private meta structure chain_progress ( α : Type ) ( m : Type → Type ) [monad m] :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (m α) )

open nat tactic

private meta def chain' { α : Type } { m : Type → Type } [monad m] [has_orelse m] ( tactics : list (m α) ) 
    : chain_progress α m → m (list α)
| ⟨ 0     , _      , _       ⟩ := fail "chain iteration limit exceeded"
| ⟨ _     , results, []      ⟩ := pure results
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                   (pure results)
                                   (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
)
