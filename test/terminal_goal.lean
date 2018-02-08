import tidy.recover
import tidy.fsplit

private structure C :=
 ( w : Type )
 ( x : list w )
 ( y : Type )
 ( z : prod w y )

 private def test_terminal_goal : C :=
 begin
 fsplit,
 success_if_fail { terminal_goal },
 exact ℕ,
 terminal_goal,
 exact [],
 success_if_fail { terminal_goal },
 exact bool,
 terminal_goal,
 exact (0, tt)
 end     