import tidy.rewrite_all_wrappers

namespace tidy.rewrite_search

universe u

@[derive decidable_eq]
inductive side
| L
| R
def side.other : side → side
| side.L := side.R
| side.R := side.L
def side.to_string : side → string
| side.L := "L"
| side.R := "R"
instance : has_to_string side := ⟨side.to_string⟩

@[derive decidable_eq]
structure sided_pair (α : Type u) :=
  (l r : α)
namespace sided_pair
variables {α : Type} (p : sided_pair α)

def get : side → α
| side.L := p.l
| side.R := p.r

def set : side → α → sided_pair α
| side.L v := ⟨v, p.r⟩
| side.R v := ⟨p.l, v⟩

def flip : sided_pair α := ⟨p.r, p.l⟩

def to_list : list α := [p.l, p.r]

def to_string [has_to_string α] (p : sided_pair α) : string :=
  to_string p.l ++ "-" ++ to_string p.r
instance has_to_string [has_to_string α] : has_to_string (sided_pair α) := ⟨to_string⟩

end sided_pair

inductive how
| rewrite (rule_index : ℕ) (side : side) (location : ℕ)
| defeq
| simp  -- TODO handle "explaining" me

meta structure rewrite :=
(e   : expr)
(prf : tactic expr) -- we defer constructing the proofs until they are needed
(how : how)

meta structure config extends rewrite_all_cfg :=
(rs              : list (expr × bool))
(max_iterations  : ℕ)
(max_discovers   : ℕ)
(trace           : bool)
(trace_summary   : bool)
(trace_result    : bool)
(trace_discovery : bool)
(exhaustive      : bool)

end tidy.rewrite_search