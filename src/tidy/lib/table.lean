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

class indexed (α : Type u) :=
(index : α → table_ref)
class keyed (α : Type u) (κ : Type v) [decidable_eq κ] :=
(key : α → κ)

-- TODO support array-backed tables

structure table (α : Type u) :=
(next_id : table_ref)
(entries : list α)

variables {α : Type u} {β : Type v} {κ : Type w} [decidable_eq κ] (t : table α)

def table.create : table α := ⟨ table_ref.first, [] ⟩
def table.from_list (l : list α) : table α := ⟨ l.length, l ⟩

def table.length := t.entries.length
def table.to_list : list α := t.entries

def table.alloc (a : α) : table α :=
  { t with next_id := t.next_id.next, entries := t.entries.concat a }
meta def table.get (r : table_ref) : tactic α := t.entries.nth r
def table.iget [inhabited α] (r : table_ref) : α := (t.entries.nth r).iget
def table.set (r : table_ref) (a : α) : table α :=
  { t with entries := t.entries.set_at r a }
def table.update [indexed α] (a : α) : table α := t.set (indexed.index a) a

def table_find_aux [decidable_eq κ] [keyed α κ] (key : κ) : list α → option α
| [] := none
| (a :: rest) := if key = @keyed.key α κ _ _ a then a else table_find_aux rest
def table.find [decidable_eq κ] [keyed α κ] (key : κ) : option α := table_find_aux key t.entries

def table.map  (f : α → β) : table β := ⟨t.next_id, t.entries.map f⟩
def table.mmap {m : Type v → Type z} [monad m] (f : α → m β) : m (table β) := do
  new_entries ← t.entries.mmap f,
  return ⟨t.next_id, new_entries⟩

meta instance [has_to_format α] : has_to_format (table α) := ⟨λ t, has_to_format.to_format t.to_list⟩