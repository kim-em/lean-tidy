-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.at_least_one

open tactic
meta def injections : tactic unit :=
do l ← local_context,
   at_least_one $ l.map $ λ e, injection e >> skip
