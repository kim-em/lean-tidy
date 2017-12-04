import ..tidy.profiling

open tactic

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