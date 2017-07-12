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

meta def stateful_tactic (σ : Type) := interaction_monad (tactic_state × σ)

@[reducible] meta def tactic_state_pure { α : Type } ( a : α ) ( ts : tactic_state ) : tactic_state :=
begin
  have p := @pure tactic _ _ a ts,
  induction p with _ ts' _ _ ts'',
  exact ts',
  exact ts''
end

meta def unreachable {α : Sort u} : α := undefined_core "unreachable"

meta instance stateful_tactic_monad (σ : Type) : monad (stateful_tactic σ) := { 
  pure   := λ { α : Type } ( a : α ) ( s : tactic_state × σ ), 
              result.success a (tactic_state_pure a s.1, s.2),
  bind   := λ { α β : Type } ( t : stateful_tactic σ α ) ( f : α → stateful_tactic σ β ) ( s : tactic_state × σ ), 
              match (t s) with
              | result.success a s' := f a s'
              | result.exception pos msg s' := result.exception pos msg s'
              end,
  id_map     := begin tidy, generalize (x (fst, snd)) X, intros, induction X, tidy, end,
  pure_bind  := begin tidy, end,
  bind_assoc := begin tidy, generalize (x (fst, snd)) X, intros, induction X, tidy, end,            
}

meta instance stateful_tactic_monad_fail (σ : Type) : monad_fail (stateful_tactic σ) := {
  stateful_tactic_monad σ with
  fail   := λ { α : Type } (msg : string) ( s : tactic_state × σ ),
              match (@tactic.fail α string _ msg) s.1 with
              | result.success a ts := unreachable
              | result.exception pos msg ts := result.exception pos msg (ts, s.2)
              end,
}

meta instance stateful_tactic_has_orelse (σ : Type) : has_orelse (stateful_tactic σ) := {
  orelse := λ { α : Type } ( t₁ : (stateful_tactic σ) α ) ( t₂ : (stateful_tactic σ) α ) ( s : tactic_state × σ ), 
              match (t₁ s) with
              | result.success a s' := result.success a s'
              | result.exception pos msg s' := t₂ s'
              end,
}

structure profiling_state :=
  ( invocations : nat )

meta def profiling_tactic := stateful_tactic profiling_state

meta def lift_tactic_to_profiling_tactic { α : Type u } ( t : tactic α ) : profiling_tactic α := 
λ ( s : tactic_state × profiling_state ), 
              match (t s.1) with
              | result.success a s' := result.success a (s', ⟨ s.2.invocations + 1 ⟩ )
              | result.exception pos msg s' := result.exception pos msg (s', ⟨ s.2.invocations + 1 ⟩ )
              end

meta instance : tactical_monad profiling_tactic := {
  stateful_tactic_monad_fail profiling_state with 
  orelse := (stateful_tactic_has_orelse profiling_state).orelse,
  lift   := λ { α : Type }, lift_tactic_to_profiling_tactic
}

meta def empty_profiling_state : profiling_state := ⟨ 0 ⟩ 

meta def profiling
  { α : Type } ( t : profiling_tactic α )
  ( success_handler   : profiling_state → tactic unit := λ p, trace format!"success, with {p.invocations} invocations" ) 
  ( exception_handler : profiling_state → tactic unit := λ p, trace format!"failed, with {p.invocations} invocations" ) 
    : tactic (α × profiling_state) :=
λ s, match t (s, empty_profiling_state) with
     | result.success a ts         :=
         match success_handler ts.2 ts.1 with
         | result.success _ _             := result.success (a, ts.2) ts.1
         | result.exception msg' pos' ts' := result.exception msg' pos' ts'  -- Ugh, an exception in the exception handler!
         end        
     | result.exception msg pos ts := 
         match exception_handler ts.2 ts.1 with
         | result.success _ _             := result.exception msg pos ts.1
         | result.exception msg' pos' ts' := result.exception msg' pos' ts'  -- Ugh, an exception in the exception handler!
         end
     end 

lemma profile_test : true :=
begin
profiling $ skip >> skip,             -- 2
profiling $ skip >> skip >> skip,     -- 3
success_if_fail { profiling $ done }, -- 1

profiling $ skip <|> done,            -- 1
profiling $ done <|> skip,            -- 2

profiling $ (skip <|> done) >> skip,  -- 2

profiling $ done <|> done <|> skip,   -- 3

success_if_fail { profiling $ done <|> done }, -- 2

triv
end

structure loop_detection_state := 
  ( past_goals : list string )

meta def loop_detection_tactic := stateful_tactic loop_detection_state

meta def lift_tactic_to_loop_detection_tactic { α : Type u } ( t : tactic α ) : loop_detection_tactic α := 
λ ( s : tactic_state × loop_detection_state ), 
              match (t s.1) with
              | result.success a s'         := match (hash_target s') with
                                               | result.success hash s'' := if s.2.past_goals.mem hash then
                                                                              match (@tactic.fail α string _ "detected looping") s'' with -- FIXME this duplicates code above
                                                                              | result.success a ts := unreachable
                                                                              | result.exception pos msg ts := result.exception pos msg (ts, s.2)
                                                                              end
                                                                            else 
                                                                              result.success a (s', ⟨ hash :: s.2.past_goals ⟩ )
                                               | _                       := unreachable
                                               end
              | result.exception pos msg s' := result.exception pos msg (s', s.2 )
              end

meta def detect_looping
  { α : Type } ( t : loop_detection_tactic α )
    : tactic α :=
λ s, match t (s, ⟨ [] ⟩ ) with
     | result.success a s'          := result.success a s'.1
     | result.exception pos msg s' := result.exception pos msg (s'.1)
     end

meta instance : tactical_monad loop_detection_tactic := {
  stateful_tactic_monad_fail loop_detection_state with 
  orelse := (stateful_tactic_has_orelse loop_detection_state).orelse,
  lift   := λ { α : Type }, lift_tactic_to_loop_detection_tactic
}


lemma looping_test : true :=
begin
detect_looping $ skip,
success_if_fail { detect_looping $ skip >> skip },

triv
end

-- PROJECT: now for a challenge --- how can we use both of the examples above at once?
