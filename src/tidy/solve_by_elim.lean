import tactic.interactive

-- TODO port to mathlib
meta def solve_by_elim' (asms : option (list expr) := none) (discharger : tactic unit := tactic.done) : opt_param ℕ 3 → tactic unit
| 0     := tactic.done
| (n+1) := discharger <|> (tactic.interactive.apply_assumption asms $ solve_by_elim' n)
