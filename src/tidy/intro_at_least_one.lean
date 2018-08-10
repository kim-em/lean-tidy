-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .repeat_at_least_once

open tactic

meta def intro_at_least_one : tactic (list string) :=
repeat_at_least_once intro1 >>= λ p, return ((p.1 :: p.2).map (λ e, e.to_string))