-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

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

 -- verifying that terminal_goal correctly considers all propositional goals as terminal?
private structure foo :=
(x : ℕ)
(p : x = 0)

open tactic
private lemma bar : ∃ F : foo, F = ⟨ 0, by refl ⟩ := 
begin
    split,
    swap,
    split,
    terminal_goal,
    swap,
    success_if_fail { terminal_goal },
    exact 0,
    refl,
    refl,
end

private structure D :=
 ( w : ℕ → Type )
 ( x : list (w 0) )
 
 private def test_terminal_goal : D :=
 begin
    split,
    swap,
    success_if_fail { terminal_goal },
    intros,
    success_if_fail { terminal_goal },
    exact ℕ,
    exact []
 end     
