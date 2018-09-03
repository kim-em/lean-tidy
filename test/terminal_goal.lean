-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tidy.recover

structure C :=
 ( w : Type )
 ( x : list w )
 ( y : Type )
 ( z : prod w y )

def test_terminal_goal : C :=
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
structure foo :=
(x : ℕ)
(p : x = 0)

open tactic
lemma bar : ∃ F : foo, F = ⟨ 0, by refl ⟩ :=
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

structure D :=
 ( w : ℕ → Type )
 ( x : list (w 0) )

def test_terminal_goal' : D :=
 begin
    split,
    swap,
    success_if_fail { terminal_goal },
    intros,
    success_if_fail { terminal_goal },
    exact ℕ,
    exact []
 end

def f : unit → Type := λ _, ℕ

def test_terminal_goal'' : Σ x : unit, f x :=
 begin
    split,
    terminal_goal,
    swap,
    terminal_goal,
    exact (),
    dsimp [f],
    exact 0
 end

def test_subsingleton_goal : 0 = 0 :=
begin
 subsingleton_goal,
 refl
end

def test_subsingleton_goal' : list ℕ :=
begin
 success_if_fail { subsingleton_goal },
 exact []
end