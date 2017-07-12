import .if_then_else
import .tidy

universe variables u v w

meta class tactical_monad (state : Type) [m : monad (interaction_monad state)] extends monad_fail (interaction_monad state), has_orelse (interaction_monad state) :=
  ( lift : Π { α : Type u }, tactic α → (interaction_monad state) α )

meta def failed {α : Type u} {state : Type} [tactical_monad state]: (interaction_monad state) α := monad_fail.fail (interaction_monad state) ""
meta def fail   {α : Type u} {state : Type} [tactical_monad state] {β : Type u} [has_to_format β] (msg : β) : (interaction_monad state) α :=
  monad_fail.fail (interaction_monad state) (to_fmt msg).to_string

meta instance lift_tactic_coe {α : Type u} (state : Type) [m : monad (interaction_monad state)] [tm : @tactical_monad state m] : has_coe (tactic α) ((interaction_monad state) α) := ⟨ @tactical_monad.lift _ m tm _ ⟩

meta instance trivial_tactical_monad : tactical_monad tactic_state := {
  interaction_monad.monad with
  fail   := λ { α : Type }, tactic.fail,
  orelse := λ { α : Type }, interaction_monad_orelse,
  lift   := λ { α : Type }, id
}

meta structure chain_progress {state : Type} (α : Type u) :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list ((interaction_monad state) α) )

open nat tactic

private meta def chain' {α : Type u} {state : Type} [tm : tactical_monad state] ( tactics : list ((interaction_monad state) α) ) 
    : chain_progress α → (interaction_monad state) (list α)
| ⟨ 0     , _      , _       ⟩ := fail "chain iteration limit exceeded"
| ⟨ _     , results, []      ⟩ := pure results
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                   (pure results)
                                   (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
)
