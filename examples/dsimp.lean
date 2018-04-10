meta def dsimp' := `[dsimp {unfold_reducible := tt, md := semireducible}]

lemma foo : 3 + 4 = 7 := 
begin
 dsimp', -- I'd really like dsimp' to not muck + up like this.
end