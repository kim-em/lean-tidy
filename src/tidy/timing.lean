
-- import system.io

-- open tactic

-- universe variables u

-- -- There's apparently about a 1/5th of a second overhead here...
-- meta def time_in_nanos : tactic ℕ :=
-- do time ← tactic.run_io (λ [ioi : io.interface], @io.cmd ioi { cmd := "gdate", args := [ "+%s%N" ] } ),
--    pure time.to_nat

-- meta def time_tactic { α : Type } ( t : tactic α ) : tactic (α × ℕ) :=
-- do time_before ← time_in_nanos,
--    r ← t,
--    time_after ← time_in_nanos,
--    pure (r, time_after - time_before)

-- -- lemma f : 1 = 1 := 
-- -- begin
-- -- (time_tactic skip) >>= trace,
-- -- simp     
-- -- end