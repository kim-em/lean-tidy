import tidy.rewrite_all
import .table

universe u

namespace tidy.rewrite_search

inductive how
| rewrite (rule_index : ℕ) (side : side) (location : ℕ) : how
| defeq

meta inductive search_result
| success (proof : expr) (steps : list how) : search_result
| failure (message : string) : search_result

inductive bound_progress (β : Type u)
| exactly : ℚ → β → bound_progress
| at_least : ℚ → β → bound_progress

open bound_progress

def bound_progress.bound {β : Type u} : bound_progress β → ℚ
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
(proof : expr)
(how   : how)

structure token :=
(id                : table_ref)
(str               : string)
(lhs_freq rhs_freq : ℕ)
def token.inc (t : token) : side → token
| side.L := { t with lhs_freq := t.lhs_freq + 1}
| side.R := { t with rhs_freq := t.rhs_freq + 1}
def token.freq (t : token) : side → ℕ
| side.L := t.lhs_freq
| side.R := t.rhs_freq

def null_token : token :=
⟨ null_table_ref, "__NULLTOKEN", 0, 0 ⟩

instance token.inhabited : inhabited token := ⟨null_token⟩
instance token.indexed : indexed token := ⟨λ t, t.id⟩
instance token.keyed : keyed token string := ⟨λ v, v.str⟩

def find_or_create_token (tokens : table token) (s : side) (tstr : string) : table token × token :=
match tokens.find tstr with
| none := do
  let t : token := ⟨tokens.next_id, tstr, 0, 0⟩,
  let t := t.inc s in (tokens.alloc t, t)
| (some t) := do
  let t := t.inc s in (tokens.update t, t)
end

meta structure vertex :=
(id      : table_ref)
(exp     : expr)
(pp      : string)
(tokens  : list table_ref)
(root    : bool)
(visited : bool)
(s       : side)
(parent  : option edge)
(adj     : list edge)

meta def vertex.same_side (a b : vertex) : bool := a.s = b.s
meta def vertex.to_string (v : vertex) : string := v.s.to_string ++ v.pp

meta def null_expr : expr := default expr
meta def null_vertex : vertex :=
⟨ null_table_ref, null_expr, "__NULLEXPR", [], ff, ff, side.L, none, [] ⟩

meta instance vertex.inhabited : inhabited vertex := ⟨null_vertex⟩
meta instance vertex.indexed : indexed vertex := ⟨λ v, v.id⟩
meta instance vertex.keyed : keyed vertex string := ⟨λ v, v.pp⟩
meta instance vertex.has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩

@[derive decidable_eq]
structure pair :=
  (l r : table_ref)
def pair.side (p : pair) (s : side) : table_ref :=
match s with
| side.L := p.l
| side.R := p.r
end
def pair.flip (p : pair) : pair := ⟨p.r, p.l⟩
def pair.to_string (c : pair) : string :=
  (c.l.to_string) ++ "-" ++ (c.r.to_string)
instance pair.has_to_string : has_to_string pair := ⟨pair.to_string⟩

structure dist_estimate (state_type : Type u) extends pair :=
  (id : table_ref)
  (bnd : bound_progress state_type)
def dist_estimate.side {α : Type u} (de : dist_estimate α) (s : side) : table_ref :=
  de.to_pair.side s
def dist_estimate.to_string {α : Type u} (de : dist_estimate α) : string :=
(pair.to_string de.to_pair) ++ "Δ" ++ de.bnd.to_string
def dist_estimate.set_bound {α : Type u} (de : dist_estimate α) (bnd : bound_progress α) : dist_estimate α := { de with bnd := bnd }

instance dist_estimate.has_to_string {α : Type u} : has_to_string (dist_estimate α) := ⟨λ v, v.to_string⟩
instance dist_estimate.indexed {α : Type u} : indexed (dist_estimate α) := ⟨λ v, v.id⟩
instance dist_estimate.keyed {α : Type u} : keyed (dist_estimate α) pair := ⟨λ v, v.to_pair⟩

meta inductive status
| continue : status
| repeat : status
| done : edge → status
| abort : string → status

inductive init_result (γ : Type)
| success : γ → init_result
| failure : string → init_result

meta structure config extends rewrite_all_cfg :=
(rs            : list (expr × bool))
(trace         : bool := ff)
(trace_summary : bool := ff)
(trace_result  : bool := ff)
(exhaustive    : bool := ff)

meta structure tracer (α β γ δ : Type) :=
(init             : tactic (init_result δ))
(publish_vertex   : δ → vertex → tactic unit)
(publish_edge     : δ → edge → tactic unit)
(publish_visited  : δ → vertex → tactic unit)
(publish_finished : δ → list edge → tactic unit)
(dump             : δ → string → tactic unit)
(pause            : δ → tactic unit)

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

meta def update_fn (α β γ δ : Type) : Type := search_state α β γ δ → ℕ → tactic (search_state α β γ δ)
meta def init_bound_fn (α β γ δ : Type) := search_state α β γ δ → vertex → vertex → bound_progress γ
meta def improve_estimate_fn (α β γ δ : Type) := search_state α β γ δ → ℚ → vertex → vertex → bound_progress γ → bound_progress γ

meta structure metric (α β γ δ : Type) :=
(init : β)
(update : update_fn α β γ δ)
(init_bound : init_bound_fn α β γ δ)
(improve_estimate_over : improve_estimate_fn α β γ δ)

meta def startup_fn (α β γ δ : Type) : Type := search_state α β γ δ → metric α β γ δ → vertex → vertex → tactic (search_state α β γ δ)
meta def step_fn (α β γ δ : Type) : Type := search_state α β γ δ → metric α β γ δ → ℕ → tactic (search_state α β γ δ × status)

meta structure strategy (α β γ δ : Type) :=
(init : α)
(startup : startup_fn α β γ δ)
(step : step_fn α β γ δ)

meta structure inst (α β γ δ : Type) :=
(metric   : metric α β γ δ)
(strategy : strategy α β γ δ)
(g        : search_state α β γ δ)

namespace search_state
variables {α β γ δ : Type} (g : search_state α β γ δ)

meta def mutate_strat (new_state : α) : search_state α β γ δ :=
{ g with strat_state := new_state }

meta def mutate_metric (new_state : β) : search_state α β γ δ :=
{ g with metric_state := new_state }

meta def set_vertex (v : vertex) : (search_state α β γ δ) :=
{ g with vertices := g.vertices.set v.id v }

meta def lookup_pair (p : pair) : tactic (vertex × vertex) := do
vf ← g.vertices.get p.l, vt ← g.vertices.get p.r, return (vf, vt)

meta def get_endpoints (e : edge) : tactic (vertex × vertex) := do
vf ← g.vertices.get e.f, vt ← g.vertices.get e.t, return (vf, vt)

meta def get_estimate_verts (de : dist_estimate γ) : tactic (vertex × vertex) := g.lookup_pair de.to_pair

end search_state

end tidy.rewrite_search