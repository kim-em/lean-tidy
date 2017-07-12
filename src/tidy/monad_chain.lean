import .if_then_else
import .tidy

universe variables u v w

meta class tactical_monad (m : Type u → Type v) extends monad_fail m, has_orelse m :=
  ( lift : Π { α : Type u }, tactic α → m α )

meta def failed {α : Type u} { m : Type u → Type v } [tactical_monad m]: m α := monad_fail.fail m ""
meta def fail {α : Type u} { m : Type u → Type v } [tactical_monad m] {β : Type u} [has_to_format β] (msg : β) : m α :=
  monad_fail.fail m (to_fmt msg).to_string

meta instance lift_tactic_coe (α : Type u) (m : Type u → Type v) [tactical_monad m]: has_coe (tactic α) (m α) :=
⟨ tactical_monad.lift _ ⟩

private meta structure chain_progress ( α : Type ) ( m : Type → Type ) [monad m] :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (m α) )

open nat tactic

private meta def chain' { α : Type } { m : Type → Type } [tactical_monad m] ( tactics : list (m α) ) 
    : chain_progress α m → m (list α)
| ⟨ 0     , _      , _       ⟩ := fail "chain iteration limit exceeded"
| ⟨ _     , results, []      ⟩ := pure results
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                   (pure results)
                                   (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
)

meta instance trivial_tactical_monad : tactical_monad tactic := {
  interaction_monad.monad with
  fail   := λ { α : Type }, tactic.fail,
  orelse := λ { α : Type }, interaction_monad_orelse,
  lift   := λ { α : Type }, id
}

meta def skip2 : tactic ( list unit ) := let tactics := [skip, skip] in chain' tactics ⟨ 0, [], tactics ⟩

structure profiling_state :=
  ( invocations : nat )

meta def stateful_tactic (β : Type) (α : Type) := β → tactic ((interaction_monad.result tactic_state α) × β)

meta def profiling_tactic := stateful_tactic profiling_state

meta def tactic_pure { α : Type } ( a : α ) : tactic α := pure a

meta def unreachable {α : Sort u} : α := undefined_core "unreachable"

meta instance profiling_tactical_monad : tactical_monad profiling_tactic := { 
  pure   := λ { α : Type } ( a : α ) ( s : profiling_state ) ( ts : tactic_state ),
              match ((tactic_pure a) ts) with
              | (result.success a ts')         := result.success (result.success a ts', s) ts'
              | (result.exception msg pos ts') := unreachable
              end,
  bind   := λ { α β : Type } ( t : profiling_tactic α ) ( f : α → profiling_tactic β ) ( s : profiling_state ) ( ts : tactic_state ),
              match (t s ts) with
              | (result.success r ts')         := match r with 
                                                  | (result.success a ts',         ps') := f a ps' ts'
                                                  | (result.exception msg pos ts', ps') := result.success (result.exception msg pos ts', ps') ts'
                                                  end
              | (result.exception msg pos ts') := unreachable
              end,
  fail   := λ { α : Type } (msg : string) ( s : profiling_state ), (do @tactic.fail _ string _ msg),
  orelse := λ { α : Type } ( t : profiling_tactic α ) ( t' : profiling_tactic α ) ( s : profiling_state ) ( ts : tactic_state ),
              match (t s ts) with
              | (result.success r ts')         := match r with 
                                                  | (result.success a ts',         ps') := (result.success r ts')
                                                  | (result.exception msg pos ts', ps') := t' ps' ts'
                                                  end
              | (result.exception msg pos ts') := unreachable
              end,
  lift   := λ { α : Type } ( t : tactic α ) ( s : profiling_state ) ( ts : tactic_state ),
              match (t ts) with
              | (result.success a ts')         := result.success (result.success a ts', ⟨ s.invocations + 1 ⟩ ) ts'
              | (result.exception msg pos ts') := result.success (result.exception msg pos ts', ⟨ s.invocations + 1 ⟩) ts'
              end,
  id_map     := begin tidy, end,
  pure_bind  := undefined,
  bind_assoc := undefined,            
}

meta def empty_profiling_state : profiling_state := ⟨ 0 ⟩ 

meta def profiling { α : Type } ( t : profiling_tactic α ) : tactic (ℕ × α) :=
do r ← t empty_profiling_state,
   trace r.2.invocations,
   match r.1 with 
   | result.success a ts := pure (r.2.invocations, a)
   | result.exception msg pos ts := match msg with
                                    | (some m) := tactic.fail ( m () )
                                    | none     := tactic.failed
                                    end
   end

lemma f : true :=
begin
profiling $ skip >> skip,             -- 2
profiling $ skip >> skip >> skip,     -- 3
success_if_fail { profiling $ done }, -- 1

profiling $ skip <|> done,            -- 1
profiling $ done <|> skip,            -- 2

profiling $ (skip <|> done) >> skip, -- 2

profiling $ done <|> done <|> skip, -- 3

success_if_fail { profiling $ done <|> done }, -- 2

triv
end