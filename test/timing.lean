import tidy.timing

open tactic

private lemma f : 1 = 1 := 
begin
(time_tactic skip) >>= trace,
simp     
end
