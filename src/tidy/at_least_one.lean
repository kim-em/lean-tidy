-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import data.option

open tactic

meta def at_least_one {α} (tactics : list (tactic α)) : tactic (list α) := 
do 
  options ← monad.sequence (tactics.map (λ t, try_core t)),
  let results := options.bind option.to_list,
  guard ¬ results.empty,
  return results