-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.profiling

open tactic

namespace tidy.test

-- TODO It would be nice to have 'begin[profiling]'
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

end tidy.test

