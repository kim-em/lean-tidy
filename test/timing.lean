-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.timing

open tactic

private lemma f : 1 = 1 :=
begin
    (time_tactic skip) >>= trace,
    simp
end
