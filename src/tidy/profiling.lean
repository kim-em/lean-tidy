import .if_then_else
import .tidy

open tactic

universe variables u v w

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

meta instance tactic_lift_coe (τ : Type) [tactic_lift τ] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad (σ × τ) α) :=
⟨ tactic_lift.lift τ ⟩

meta instance interaction_monad.has_orelse (σ : Type) : has_orelse (interaction_monad σ) := {
  orelse := λ { α : Type } (t₁ t₂ : interaction_monad σ α) s, 
              match (t₁ s) with
              | result.success   a       s' := result.success a s'
              | result.exception msg pos s' := match (t₂ s') with
                                               | result.success   a'        s'' := result.success   a'        s''
                                               | result.exception msg' pos' s'' := result.exception msg' pos' s''
                                               end
              end
}

--- Profiling:

structure invocation_count := 
  ( invocations : ℕ )

meta def exception_in_messages {α : Sort u} : α := undefined_core "exception in profiling messages!"

meta def profiling
  { σ α : Type } 
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × invocation_count) α ) 
  ( success_handler   : invocation_count → tactic unit := λ p, trace format!"success, with {p.invocations} invocations" ) 
  ( exception_handler : invocation_count → tactic unit := λ p, trace format!"failed, with {p.invocations} invocations" ) 
    : interaction_monad σ (α × invocation_count) :=
λ s, match t (s, ⟨ 0 ⟩) with
     | result.success a ts         :=
         match success_handler ts.2 ts.1 with
         | result.success _ _             := result.success (a, ts.2) ts.1
         | result.exception msg' pos' ts' := exception_in_messages  -- Ugh, an exception in the exception handler!
         end        
     | result.exception msg pos ts := 
         match exception_handler ts.2 ts.1 with
         | result.success _ _             := result.exception msg pos ts.1
         | result.exception msg' pos' ts' := exception_in_messages  -- Ugh, an exception in the exception handler!
         end
     end 

meta instance lift_to_profiling_tactic : tactic_lift invocation_count := 
{
  lift := λ { σ α : Type } [underlying_tactic_state σ] ( t : interaction_monad σ α ) (s : σ × invocation_count),
            match t s.1 with
            | result.success   a       ts := result.success   a       (ts, ⟨ s.2.invocations + 1 ⟩ )
            | result.exception msg pos ts := result.exception msg pos (ts, ⟨ s.2.invocations + 1 ⟩ )
            end
} 

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

meta def unreachable {α : Sort u} : α := undefined_core "unreachable"

meta def detect_looping
  { σ α : Type } 
  [ underlying_tactic_state σ ]
  ( t : interaction_monad (σ × loop_detection_state) α ) 
    : interaction_monad σ α :=
λ s, match (hash_target s) with
     | result.success   hash    s' := match t (s, ⟨ [ hash ] ⟩ ) with
                                      | result.success a s''         := result.success a s''.1
                                      | result.exception pos msg s'' := result.exception pos msg (s''.1)
                                      end
     | result.exception pos msg s' := unreachable
     end

meta instance lift_to_loop_detection_tactic : tactic_lift loop_detection_state := 
{
  lift := λ { σ α : Type } [uts : underlying_tactic_state σ] ( t : interaction_monad σ α ) (s : σ × loop_detection_state),
            match t s.1 with
            | result.success   a       s' := match (hash_target (@underlying_tactic_state.to_tactic_state _ uts s')) with -- FIXME why doesn't the coercion work? why can't Lean find uts itself?
                                             | result.success hash s'' := if s.2.past_goals.mem hash then
                                                                            match (@tactic.fail α string _ ("detected looping\n" ++ s.2.past_goals.to_string ++ "\n" ++ hash)) s'' with -- FIXME this duplicates code above
                                                                            | result.success   a       s''' := unreachable
                                                                            | result.exception pos msg s''' := result.exception pos msg (s', s.2)
                                                                            end
                                                                          else  
                                                                            result.success a (s', ⟨ hash :: s.2.past_goals ⟩ )
                                             | _ := unreachable
                                             end
            | result.exception msg pos s' := result.exception msg pos (s', s.2)
            end
} 

meta def simp := `[simp]

lemma looping_test_1 (a : empty): 1 = 1 :=
begin
success_if_fail { detect_looping $ skip },
success_if_fail { detect_looping $ skip >> skip },
refl
end
lemma looping_test_2 (a : empty): 1 = 1 :=
begin
detect_looping $ simp
end

-- Lean won't chain two coercions together for us, so we provide a shortcut here.
meta instance tactic_lift_twice_coe (τ τ' : Type) [tactic_lift τ] [tactic_lift τ'] (σ α : Type) [underlying_tactic_state σ] : has_coe (interaction_monad σ α) (interaction_monad ((σ × τ) × τ') α) :=
⟨ λ t, tactic_lift.lift τ' (tactic_lift.lift τ t) ⟩

lemma looping_and_profiling_at_the_same_time_test_1 : true :=
begin
profiling $ (detect_looping $ triv),
end
lemma looping_and_profiling_at_the_same_time_test_2 : true :=
begin
success_if_fail { profiling $ detect_looping $ skip >> skip },
triv
end

