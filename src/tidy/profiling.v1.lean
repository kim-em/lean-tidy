-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

/-
This is just a minimal instantiation of a profiling framework.
It's wrong, because it can't handle failure.
-/
structure profiling_state :=
  ( invocations : nat )
  ( failure     : bool )

meta def profiling_tactic :=
state_t profiling_state tactic

meta instance : has_append profiling_state :=
⟨ λ ( p q : profiling_state ), ⟨ p.invocations + q.invocations, p.failure ∨ q.failure ⟩ ⟩

meta instance : monad profiling_tactic :=
state_t.monad _ _

meta def count_invocations { α : Type } ( t : tactic α ) : profiling_tactic α :=
λ p, do o ← try_core t,
        match o with
        | (some r) := pure (r, ⟨ p.invocations + 1, ff ⟩)
        | none     := pure (begin admit end, ⟨ p.invocations + 1, tt ⟩)
        end

meta instance : monad.has_monad_lift tactic profiling_tactic :=
⟨ @count_invocations ⟩ 

meta instance (α : Type) : has_coe (tactic α) (profiling_tactic α) :=
⟨ monad.monad_lift ⟩

-- FIXME this is incorrect! We need to preserve profiling information from failed branches.
meta def profiling_tactic_orelse {α : Type} (t₁ t₂ : profiling_tactic α) : profiling_tactic α :=
λ ss ts, result.cases_on (t₁ ss ts)
  result.success
  (λ e₁ ref₁ s', result.cases_on (t₂ ss ts)
     result.success
     result.exception)

meta instance : monad_fail profiling_tactic :=
{ profiling_tactic.monad with fail := λ α s, (tactic.fail (to_fmt s) : profiling_tactic α) }

meta instance : alternative profiling_tactic :=
{ profiling_tactic.monad with
  failure := λ α, @tactic.failed α,
  orelse  := @profiling_tactic_orelse }

meta def invocations : profiling_tactic nat :=
λ p, (do pure (p.invocations, p))

meta def empty_profiling_state : profiling_state := ⟨ 0, ff ⟩ 

meta def profiling { α : Type } ( t : profiling_tactic α ) : tactic (ℕ × α) :=
do r ← t empty_profiling_state,
   trace r.2.invocations,
   pure (r.2.invocations, r.1)

lemma f : true :=
begin
profiling $ skip >> skip,             -- 2
profiling $ skip >> skip >> skip,     -- 3
success_if_fail { profiling $ done },
profiling $ done <|> skip,            -- should be 2, but is 1.
triv
end
