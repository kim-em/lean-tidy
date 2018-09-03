/-
old chain (did not automatically abstract intermediate results)
cumulative profiling times:
	compilation 396ms
	decl post-processing 6.77ms
	elaboration 51.6s
	elaboration: tactic compilation 140ms
	elaboration: tactic execution 16.8s
	parsing 234ms
	type checking 20.5ms

new chain:
cumulative profiling times:
	compilation 377ms
	decl post-processing 7.26ms
	elaboration 14.1s
	elaboration: tactic compilation 135ms
	elaboration: tactic execution 9.57s
	parsing 231ms
	type checking 19.9ms
-/

import tidy.tidy

namespace deeply_nested

structure A :=
(z : ℕ)

structure B :=
(a : A)
(aa : a.z = 0)

structure C :=
(a : A)
(b : B)
(ab : a.z = b.a.z)

structure D :=
(a : B)
(b : C)
(ab : a.a.z = b.a.z)

structure E :=
(a : C)
(b : D)
(ab : a.b.a.z = b.b.a.z)

structure F :=
(a : D)
(b : E)
(ab : a.b.b.a.z = b.b.b.a.z)

structure G :=
(a : E)
(b : F)
(ab : a.b.b.b.a.z = b.b.b.b.a.z)

structure H :=
(a : F)
(b : G)
(ab : a.b.b.b.b.a.z = b.b.b.b.b.a.z)

structure I :=
(a : G)
(b : H)
(ab : a.b.b.b.b.b.a.z = b.b.b.b.b.b.a.z)

structure J :=
(a : H)
(b : I)
(ab : a.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.a.z)

structure K :=
(a : I)
(b : J)
(ab : a.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.a.z)

structure L :=
(a : J)
(b : K)
(ab : a.b.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.b.a.z)

structure M :=
(a : K)
(b : L)
(ab : a.b.b.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.b.b.a.z)

structure N :=
(a : L)
(b : M)
(ab : a.b.b.b.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.b.b.b.a.z)

open tactic

def f : F :=
begin
tidy --{trace_result:=tt},
-- fsplit, fsplit, fsplit, fsplit, rotate_left 1,
--  refl, tactic.result >>= tactic.trace,
--   fsplit, fsplit, rotate_left 1,
--   fsplit, fsplit, rotate_left 1, refl,
--    refl, tactic.result >>= tactic.trace,
--     refl, fsplit,
--    fsplit, fsplit, rotate_left 1, fsplit, fsplit, rotate_left 1,
--     refl, refl, fsplit, fsplit, fsplit, rotate_left 1,
--      refl, fsplit, fsplit, rotate_left 1, fsplit,
--       fsplit, rotate_left 1, refl, refl, refl, refl, refl
end.

-- #print prefix deeply_nested.f
end deeply_nested

