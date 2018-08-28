import .repeat_at_least_once
import .recover

open tactic

variables {α : Type} [has_to_format α]

meta def luxembourg_chain_aux (tac : tactic α) : ℕ → tactic (list (ℕ × α))
| b := do (done >> return []) <|>
            (do a ← tac,
                c ← luxembourg_chain_aux 0,
                return ((b, a) :: c)) <|>
            (do n ← num_goals,
                if b = (n-1) then return [] else do  
                rotate_left 1,
                luxembourg_chain_aux (b+1)).

/-- Returns a `list (ℕ × α)`, whose successive elements `(n, a)` represent
    a successful result of `rotate_left n >> tac`. 
    
    (When `n = 0`, the `rotate_left` may of course be omitted.) -/
meta def luxembourg_chain_core (tac : tactic α) : tactic (list (ℕ × α)) :=
do b ← num_goals,
   luxembourg_chain_aux tac 0


meta def luxembourg_chain (tactics : list (tactic α)) : tactic (list string) :=
do results ← luxembourg_chain_core (first tactics),
   return (results.map (λ p, (if p.1 = 0 then "" else "rotate_left " ++ (to_string p.1) ++ ", ") ++ (format!"{p.2}").to_string))
