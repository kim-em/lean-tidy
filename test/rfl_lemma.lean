-- import tidy.command.rfl_lemma

-- structure metype (A B : Type) :=
-- (v : ℕ)

-- structure a_dummy (C D : Type) :=
-- (map'      : Π {X Y : Type}, (C → X → Y) → metype C D)

-- def a_dummy.map {C D : Type} (F : a_dummy C D) {X Y : Type} (f : C → X → Y) : metype C D := F.map' f

-- def lol (E F : Type) [has_lt ℕ] : a_dummy F E :=
-- { map' := λ X Y, λ f, ⟨F, E, 42⟩ }.

-- -- We'd like one of these please:
-- @[simp] lemma lol_map2
--   (E F : Type) [has_lt ℕ] {X Y : Type} (f : F → X → Y) :
--   (lol E F).map f = ⟨F, E, 42⟩ := rfl.



-- -- Try `rfl_lemma` + `?`, trace version, both private and public mode
-- namespace eg1
-- private rfl_lemma? lol map

-- #check lol_map
-- end eg1

-- namespace eg2
-- rfl_lemma? lol map

-- #check lol_map
-- end eg2

-- -- Try `rfl_lemma` vanilla version, both private and public mode
-- namespace eg3
-- private rfl_lemma lol map

-- #check lol_map
-- end eg3

-- namespace eg4
-- rfl_lemma lol map

-- #check lol_map
-- end eg4