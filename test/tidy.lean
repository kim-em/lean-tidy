-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.tidy

open tactic

namespace tidy.test

meta def interactive_simp := `[simp]

def tidy_test_0 : ∀ x : unit, x = unit.star := 
begin
  success_if_fail { chain {} [ interactive_simp ] },
  intro1,
  induction x,
  refl
end
def tidy_test_1 (a : string): ∀ x : unit, x = unit.star := 
begin
  tidy
end
def tidy_test_2 (a : string): ∀ x : unit, x = unit.star := 
begin
  tidy {trace_steps:=tt, trace_result:=tt}
end

end tidy.test