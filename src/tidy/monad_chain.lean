universe variables u v w

meta class tactical_monad (m : Type u → Type v) extends monad_fail m, has_orelse m :=
  ( lift : Π { α : Type u }, tactic α → m α )

meta def failed {α : Type u} { m : Type u → Type v } [tactical_monad m]: m α := monad_fail.fail m ""
meta def fail {α : Type u} { m : Type u → Type v } [tactical_monad m] {β : Type u} [has_to_format β] (msg : β) : m α :=
  monad_fail.fail m (to_fmt msg).to_string

meta instance lift_tactic_coe (α : Type u) (m : Type u → Type v) [tactical_monad m]: has_coe (tactic α) (m α) :=
⟨ tactical_monad.lift _ ⟩

meta def if_then_else { α β : Type } { m : Type → Type } [monad m] [has_orelse m] ( i : m α ) ( t e : m β ) : m β :=
do r ← (i >> pure tt) <|> pure ff,
   if r then do t else do e

private meta structure chain_progress ( α : Type ) ( m : Type → Type ) [monad m] :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (m α) )

open nat tactic

private meta def chain' { α : Type } { m : Type → Type } [tactical_monad m] ( tactics : list (m α) ) 
    : chain_progress α m → m (list α)
| ⟨ 0, _, _ ⟩                  := fail ""
| ⟨ _, results, [] ⟩           := (pure results) 
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                   (pure results)
                                   (pure [])

meta instance trivial_tactical_monad : tactical_monad tactic := {
  interaction_monad.monad with
  fail := sorry,
  orelse := sorry,
  lift := λ { α : Type }, id
}

meta def skip2 : tactic ( list unit ) := let tactics := [skip, skip] in chain' tactics ⟨ 0, [], tactics ⟩
