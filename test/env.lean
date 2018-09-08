import system.io
import tidy.lib
import tidy.tidy

import data.polynomial
import data.analysis.filter
import data.complex.basic
import data.nat.prime
import logic.embedding

import tidy.pretty_print

def bar : 1 = 1 := rfl

open tactic
open interactive
open lean.parser
open io

@[user_command] meta def foo (_ : parse $ tk "foo") : lean.parser unit :=
do
  d ← get_decl `bar,
  let d := d.to_definition,
  (levels, type, value, reducibility, trusted) ← pure (match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    (levels, type, value, reducibility, trusted)
  | _ := undefined
  end),
  trace type,
  m ← mk_meta_var type,
  set_goals [m],
  set_goals [],
  skip.

-- foo

meta def decl_names : tactic (list name) :=
do
  e ← get_env,
  return $ e.fold [] (λ d l, d.to_name :: l)

meta def turkle : false :=
begin
(do
  d ← decl_names,
  let s := d.length,
  trace s),
  sorry
end

meta def baz (n : name) : tactic unit :=
do
  d ← get_decl n,
  let dd := d.to_definition,
  (levels, type) ← match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    pure (levels, type)
  | declaration.thm name levels type value :=
    pure (levels, type)
  | _ := failed
  end,
  -- tactic.unsafe_run_io (io.print_ln type),
  -- trace n,
  pp ← pretty_print type,
  e ← get_env,
  let ret := match  e.decl_olean n with
  | none := "???"
  | some ret := ret
  end,
  -- if (ol.split_on '/').contains "mathlib" ∨ tt then skip else failed,
  -- if (n.to_string.split_on '.').contains "to_fun_eq_coe" then skip else failed,
  -- trace n,
  -- trace format!"{n}",
  -- match n with
  -- | name.mk_string s $ name.mk_string r n := trace format!"{s} {r}"
  -- | _ := skip
  -- end,
  -- trace format!"{ol}",
  -- tactic.unsafe_run_io (io.print_ln type),
  m ← mk_meta_var type,
  gs ← get_goals,
  set_goals [m],
  trace format!"TRY:{n}@{ret}",
  -- o ← try_core `[refl],
  o ← try_core `[tactic.tidy { tactics := extended_tidy_tactics }],
  match o with
  | some _ := do trace format!"OK",
  -- trace format!"{o}",
  r ← instantiate_mvars m,
  -- trace format!"{r}",
  set_goals gs
  | none := trace format!"BAD"
  end

lemma qux : false := begin
  tactic.tidy { tactics := extended_tidy_tactics }

end

meta def baz_everything : tactic unit :=
do
  e ← get_env,
  let r := e.fold [] (λ d l, d.to_name :: l),
  trace r.length,
  -- let r := r.take 10,
  ll ← r.mmap (λ n, do ret ← try_core (baz n), return $ match ret with | none := 0 | some _ := 1 end),
  trace $ ll.foldl (λ k i, k + i) 0

def yeti : false :=
begin
  -- baz `bar,
  baz_everything,

end
