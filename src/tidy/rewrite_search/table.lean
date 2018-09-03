import tidy.lib

universes u v

def table_ref : Type := ℕ
def table_ref.from_nat (r : ℕ) : table_ref := r
def table_ref.to_nat (r : table_ref) : ℕ := r
def table_ref.to_string (r : table_ref) : string := to_string r.to_nat
def table_ref.next (r : table_ref) : table_ref := table_ref.from_nat (r + 1)
def null_table_ref  : table_ref := table_ref.from_nat 0x8FFFFFFF
def first_table_ref : table_ref := table_ref.from_nat 0

class indexed (α : Type u) :=
(index : α → table_ref)
class keyed (α : Type u) (β : Type v) [decidable_eq β] :=
(key : α → β)

structure table (α : Type u) [inhabited α] :=
(next_id : table_ref)
(entries : list α) -- FIXME use array

variables {α : Type u} {β : Type v} [decidable_eq β] [inhabited α] (t : table α)

def table.create : table α := ⟨ first_table_ref, [] ⟩
def table.from_list (l : list α) : table α := ⟨ l.length, l ⟩

def table.length := t.entries.length
def table.to_list : list α := t.entries

def table.alloc (a : α) : table α :=
  { t with next_id := t.next_id.next, entries := t.entries.concat a }
def table.at (r : table_ref) : α := t.entries.at r
def table.set (r : table_ref) (a : α) : table α :=
  { t with entries := t.entries.set_at r a }
def table.update [indexed α] (a : α) : table α := t.set (indexed.index a) a

def table_find_aux [decidable_eq β] [keyed α β] (key : β) : list α → option α
| [] := none
| (a :: rest) := if key = @keyed.key α β _ _ a then a else table_find_aux rest
def table.find [decidable_eq β] [keyed α β] (key : β) : option α := table_find_aux key t.entries