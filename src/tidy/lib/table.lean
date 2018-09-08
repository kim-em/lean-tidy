import data.list
import .list

universes u v w z

def table_ref : Type := ℕ
def table_ref.from_nat (r : ℕ) : table_ref := r
def table_ref.to_nat (r : table_ref) : ℕ := r
def table_ref.to_string (r : table_ref) : string := to_string r.to_nat
def table_ref.next (r : table_ref) : table_ref := table_ref.from_nat (r + 1)
def table_ref.null  : table_ref := table_ref.from_nat 0x8FFFFFFF
def table_ref.first : table_ref := table_ref.from_nat 0
instance : has_to_string table_ref := ⟨λ t, t.to_string⟩

class indexed (α : Type u) :=
(index : α → table_ref)
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

-- TODO support array-backed tables

structure table (α : Type u) :=
(next_id : table_ref)
(entries : list α)

namespace table

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

def create : table α := ⟨ table_ref.first, [] ⟩
def from_list (l : list α) : table α := ⟨ l.length, l ⟩

def length := t.entries.length
def to_list : list α := t.entries

def alloc (a : α) : table α :=
  { t with next_id := t.next_id.next, entries := t.entries.concat a }
def at_ref (r : table_ref) : option α := t.entries.nth r
meta def get (r : table_ref) : tactic α := t.at_ref r
def iget [inhabited α] (r : table_ref) : α := (t.entries.nth r).iget
def set (r : table_ref) (a : α) : table α :=
  { t with entries := t.entries.set_at r a }
def update [indexed α] (a : α) : table α := t.set (indexed.index a) a

private def find_aux (p : α → Prop) [decidable_pred p] : list α → option α
| [] := none
| (a :: rest) := if p a then a else find_aux rest
def find (p : α → Prop) [decidable_pred p] : option α := find_aux p t.entries
def find_key [decidable_eq κ] [keyed α κ] (key : κ) : option α := t.find (λ a, key = @keyed.key _ _ _ _ a)

def map  (f : α → β) : table β := ⟨t.next_id, t.entries.map f⟩
def mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) := do
  new_entries ← t.entries.mmap f,
  return ⟨t.next_id, new_entries⟩

def is_after_last (r : table_ref) : bool := t.next_id.to_nat <= r.to_nat

instance [has_to_string α] : has_to_string (table α) := ⟨λ t, to_string t.to_list⟩

end table