import tidy.lib.table
import data.rat

import tidy.rewrite_search.discovery.common

import .common
import .hook

universe u

namespace tidy.rewrite_search

def dnum : Type := ℤ
namespace dnum

def of_nat (n : ℕ) : dnum := int.of_nat n

instance : decidable_linear_ordered_comm_group dnum := by dunfold dnum; apply_instance
instance : has_zero dnum := int.has_zero
instance : has_one dnum := int.has_one
instance : has_add dnum := int.has_add
instance : has_mul dnum := int.has_mul
instance : inhabited dnum := int.inhabited

instance : has_to_string dnum := int.has_to_string
meta instance : has_to_format dnum := int.has_to_format

end dnum

inductive bound_progress (β : Type u)
| exactly : dnum → β → bound_progress
| at_least : dnum → β → bound_progress

open bound_progress

def bound_progress.bound {β : Type u} : bound_progress β → dnum
| (exactly n _)  := n
| (at_least n _) := n
def bound_progress.sure {β : Type u} : bound_progress β → bool
| (exactly _ _)  := tt
| (at_least _ _) := ff
def bound_progress.to_string {β : Type u} : bound_progress β → string
| (exactly n _)  := "= " ++ to_string n
| (at_least n _) := "≥ " ++ to_string n

meta structure edge :=
(f t   : table_ref)
(proof : tactic expr)
(how   : how)
namespace edge
  variables (e : edge)

  --TODO what to do about the how? Using this currently breaks backtracking
  meta def flip : edge := ⟨e.t, e.f, e.proof >>= tactic.mk_eq_symm, e.how⟩
  meta def other (r : table_ref) : option table_ref :=
    if e.f = r then e.t else
    if e.t = r then e.f else
    none

  meta instance has_to_format : has_to_format edge := ⟨λ e, format!"{e.f}->{e.t}"⟩
end edge

structure rewriterator :=
(orig : table_ref)
(front : table_ref)

meta structure vertex :=
(id       : table_ref)
(exp      : expr)
(pp       : string)
(tokens   : list table_ref)
(root     : bool)
(visited  : bool)
(s        : side)
(parent   : option edge)
(rw_prog  : option rewrite_progress)
(rws      : table rewrite)
(rw_front : table_ref)
(adj      : table edge)
namespace vertex
meta def same_side (a b : vertex) : bool := a.s = b.s
meta def to_string (v : vertex) : string := v.s.to_string ++ v.pp
meta def create (id : table_ref) (e : expr) (pp : string) (token_refs : list table_ref) (root : bool) (s : side) : vertex := ⟨ id, e, pp, token_refs, root, ff, s, none, none, table.create, table_ref.first, table.create ⟩

meta def null : vertex := vertex.create table_ref.null (default expr) "__NULLEXPR" [] ff side.L

meta instance inhabited : inhabited vertex := ⟨null⟩
meta instance indexed : indexed vertex := ⟨λ v, v.id⟩
meta instance keyed : keyed vertex string := ⟨λ v, v.pp⟩
meta instance has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩
end vertex

def pair := sided_pair table_ref
def pair.null : pair := ⟨table_ref.null, table_ref.null⟩
instance pair.has_to_string : has_to_string pair := ⟨sided_pair.to_string⟩

structure dist_estimate (state_type : Type u) extends sided_pair table_ref :=
  (id : table_ref)
  (bnd : bound_progress state_type)
namespace dist_estimate
variables {α : Type} (de : dist_estimate α)

def to_pair : pair := de.to_sided_pair
def side (s : side) : table_ref := de.to_pair.get s
def set_bound (bnd : bound_progress α) : dist_estimate α := { de with bnd := bnd }
def to_string : string := de.to_pair.to_string ++ "Δ" ++ de.bnd.to_string

instance {γ : Type} : has_to_string (dist_estimate γ) := ⟨λ v, v.to_string⟩
instance {γ : Type} : indexed (dist_estimate γ) := ⟨λ v, v.id⟩
instance {γ : Type} : keyed (dist_estimate γ) pair := ⟨λ v, v.to_pair⟩

end dist_estimate

structure token :=
(id   : table_ref)
(str  : string)
(freq : sided_pair ℕ)
namespace token
def inc (t : token) (s : side) : token := {t with freq := t.freq.set s $ (t.freq.get s) + 1}

def null : token := ⟨ table_ref.null, "__NULLTOKEN", 0, 0 ⟩

instance inhabited : inhabited token := ⟨null⟩
instance indexed : indexed token := ⟨λ t, t.id⟩
instance keyed : keyed token string := ⟨λ v, v.str⟩
end token

meta def find_or_create_token (tokens : table token) (s : side) (tstr : string) : table token × token :=
match tokens.find_key tstr with
| none := do
  let t : token := ⟨tokens.next_id, tstr, ⟨0, 0⟩⟩,
  let t := t.inc s in (tokens.alloc t, t)
| (some t) := do
  let t := t.inc s in (tokens.update t, t)
end

meta inductive status
| continue : status
| repeat : status
| done : edge → status
| abort : string → status

inductive init_result (ε : Type)
| success : ε → init_result
| failure : string → init_result

meta def init_fn (ε : Type) := tactic (init_result ε)

namespace init_result
meta def pure {ε : Type} (v : ε) : tactic (init_result ε) := return $ success v
meta def fail {ε : Type} (reason : string) : tactic (init_result ε) := return $ init_result.failure ε reason

meta def cases {ε η : Type} (name : string) (fn : init_fn ε) (next_step : ε → tactic η) (fallback : string → tactic η) : tactic η := do
  val ← fn,
  match val with
  | failure _ reason := do
    fallback reason
  | success val := do
    next_step val
  end

meta def chain {ε η : Type} (name : string) (fn : init_fn ε) (next_step : ε → init_fn η) : tactic (init_result η) :=
  cases name fn next_step $ λ reason, return $ failure _ ("An error occurred while initialising " ++ name ++ ": " ++ reason)

meta def try {ε η : Type} (name : string) (fn : init_fn ε) (next_step : ε → tactic (option η)) : tactic (option η) :=
  cases name fn next_step $ λ reason, do
    tactic.trace ("\nWarning: failed to initialise " ++ name ++ "! Reason:\n\n" ++ reason),
    return none
end init_result

meta structure tracer (α β γ δ : Type) :=
(init             : init_fn δ)
(publish_vertex   : δ → vertex → tactic unit)
(publish_edge     : δ → edge → tactic unit)
(publish_visited  : δ → vertex → tactic unit)
(publish_finished : δ → list edge → tactic unit)
(dump             : δ → string → tactic unit)
(pause            : δ → tactic unit)

structure statistics :=
(num_discovers : ℕ)
def statistics.init : statistics := ⟨0⟩

meta structure search_state (α β γ δ : Type) :=
(tr           : tracer α β γ δ)
(conf         : config)
(strat_state  : α)
(metric_state : β)
(tokens       : table token)
(vertices     : table vertex)
(estimates    : table (dist_estimate γ))
(solving_edge : option edge)
(tr_state     : δ)
(prog         : discovery.progress)
(stats        : statistics)

def LHS_VERTEX_ID : table_ref := table_ref.from_nat 0
def RHS_VERTEX_ID : table_ref := table_ref.from_nat 1

meta def update_fn (α β γ δ : Type) : Type := search_state α β γ δ → ℕ → tactic (search_state α β γ δ)
meta def init_bound_fn (α β γ δ : Type) := search_state α β γ δ → vertex → vertex → bound_progress γ
meta def improve_estimate_fn (α β γ δ : Type) := search_state α β γ δ → dnum → vertex → vertex → bound_progress γ → bound_progress γ

meta structure metric (α β γ δ : Type) :=
(init : init_fn β)
(update : update_fn α β γ δ)
(init_bound : init_bound_fn α β γ δ)
(improve_estimate_over : improve_estimate_fn α β γ δ)

meta def startup_fn (α β γ δ : Type) : Type := search_state α β γ δ → metric α β γ δ → vertex → vertex → tactic (search_state α β γ δ)
meta def step_fn (α β γ δ : Type) : Type := search_state α β γ δ → metric α β γ δ → ℕ → tactic (search_state α β γ δ × status)

meta structure strategy (α β γ δ : Type) :=
(init : init_fn α)
(startup : startup_fn α β γ δ)
(step : step_fn α β γ δ)

meta structure inst (α β γ δ : Type) :=
(metric : metric α β γ δ)
(strategy : strategy α β γ δ)
(g : search_state α β γ δ)

meta def strategy_constructor (α : Type) := Π (β γ δ : Type), strategy α β γ δ
meta def metric_constructor (β γ : Type) := Π (α δ : Type), metric α β γ δ
meta def tracer_constructor (δ : Type) := Π (α β γ : Type), tracer α β γ δ

namespace search_state
variables {α β γ δ : Type} (g : search_state α β γ δ)

meta def mutate_strat (new_state : α) : search_state α β γ δ :=
{ g with strat_state := new_state }

meta def mutate_metric (new_state : β) : search_state α β γ δ :=
{ g with metric_state := new_state }

meta def mutate_stats (new_stats : statistics) : search_state α β γ δ :=
{ g with stats := new_stats}

meta def set_vertex (v : vertex) : search_state α β γ δ × vertex :=
({ g with vertices := g.vertices.set v.id v }, v)

meta def lookup_pair (p : pair) : tactic (vertex × vertex) := do
vf ← g.vertices.get p.l, vt ← g.vertices.get p.r, return (vf, vt)

meta def get_endpoints (e : edge) : tactic (vertex × vertex) := do
vf ← g.vertices.get e.f, vt ← g.vertices.get e.t, return (vf, vt)

meta def get_estimate_verts (de : dist_estimate γ) : tactic (vertex × vertex) := g.lookup_pair de.to_pair

end search_state

meta structure proof_unit :=
(proof : expr)
(side : side)
(steps : list how)

meta inductive search_result
| success (proof : expr) (units : list proof_unit) : search_result
| failure (message : string) : search_result

end tidy.rewrite_search
