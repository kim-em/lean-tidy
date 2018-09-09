import tidy.mllist

open mllist

meta def f : nat → tactic nat
| 0 := tactic.failed
| (n+1) := tactic.trace n $> n

run_cmd fix f 10 -- prints only 9

run_cmd (fix f 10 >>= mllist.force >>= tactic.trace) -- prints 9,...,0 and [9, ..., 0]

run_cmd (do L ← fix f 10, L ← L.map (λ n, n*n), mllist.force L >>= tactic.trace) -- prints 9,...,0 and [81, ..., 0]

meta def g : nat → tactic nat
| n := tactic.trace ("g " ++ (to_string n)) $> (n*n)

run_cmd (do L ← fix f 10, L ← L.mmap g, mllist.force L >>= tactic.trace) -- prints 9,...,0 and [81, ..., 0]
