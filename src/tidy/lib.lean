import data.buffer
import data.pnat
import data.nat.basic

universe u

--FIXME the fact that we use this is really sad (ARRAYS DO IT)
def list_at {α : Type u} (default : α) : list α → ℕ → α
| [] _ := default -- FIXME catastrophic failure
| (a :: rest) k := if k = 0 then a else list_at rest (k - 1)

def list_set_at_aux {α : Type u} (val : α) : list α → list α → ℕ → list α
| _ [] _          := [] -- FIXME catastrophic failure
| l (a :: rest) 0 := l.append (val :: rest)
| l (a :: rest) k := list_set_at_aux (l.append [a]) rest (k - 1)

--FIXME the fact that we use this is really sad (ARRAYS DO IT)
def list_set_at {α : Type u} (l : list α) (idx : ℕ) (val : α) : list α :=
  list_set_at_aux val [] l idx

def list.split_on_aux {α : Type u} [decidable_eq α] (a : α) : list α → list α → list (list α) 
| [] l       := [l.reverse]
| (h :: t) l := if h = a then
                  l.reverse :: (list.split_on_aux t [])
                else
                  list.split_on_aux t (h :: l)

def list.split_on {α : Type u} [decidable_eq α] (a : α) : list α → list (list α) 
| l := list.split_on_aux a l []

def string.split_on (c : char) (s : string) := (s.to_list.split_on c).map(λ l, l.as_string)

def list.erase_such_that {α : Type u} (f : α → Prop) [decidable_pred f] : list α → list α
| [] := []
| (h :: t) := if f h then t else h :: t.erase_such_that

def list.strip {α : Type u} [decidable_eq α] (l : list α) (v : α) : list α :=
  l.erase_such_that (λ c, c = v)

def list.stripl {α : Type u} [decidable_eq α] (l : list α) (vs : list α) : list α :=
  l.erase_such_that (λ c, c ∈ vs)

def char_buffer.from_list (l : list char) : char_buffer := buffer.nil.append_list l

lemma nat.succ_pred (n : ℕ) (h : n ≠ 0) : nat.succ (nat.pred n) = n := 
begin
  cases n,
  contradiction,
  simp,
end

lemma fin.with_max (n m : ℕ) (h : m ≠ 0): fin m := 
⟨ min n (m-1), begin 
                 have p := min_le_right n (nat.pred m), 
                 have q := nat.lt_succ_of_le p, 
                 rw nat.succ_pred at q,
                 exact q,
                 assumption
               end ⟩

lemma pnat.succ_pred (n : pnat) : nat.succ (nat.pred n) = n := 
begin
  cases n with n h,
  cases n,
  have := lt_irrefl _ h ; contradiction,
  simp,
end

lemma fin.with_max' (n : ℕ) (m : pnat) : fin m := 
⟨ min n (m-1), begin 
                 have p := min_le_right n (nat.pred m), 
                 have q := nat.lt_succ_of_le p, 
                 rw nat.succ_pred at q,
                 exact q,
                 exact nat.pos_iff_ne_zero.mp m.property,
               end ⟩

def TAG_CONT    := 0b10000000
def TAG_TWO_B   := 0b11000000
def TAG_THREE_B := 0b11100000
def TAG_FOUR_B  := 0b11110000
def MAX_ONE_B   := 0x80
def MAX_TWO_B   := 0x800
def MAX_THREE_B := 0x10000

--FIXME implment me! This will get proper characters in the visualiser!
def utf8decode_char (c : char) : list char := [c]
  -- let code : nat := c.to_nat in
  -- if code < MAX_ONE_B then
  --   ⟨ code.to_char, _ ⟩
  -- else if code < MAX_TWO_B then
  --       b.push_back(:= code >> 6 & 0x1F) | TAG_TWO_B);
  --       b.push_back(:= code & 0x3F) | TAG_CONT);
  --   } else if (code < MAX_THREE_B) {
  --       b.push_back(:= code >> 12 & 0x0F) | TAG_THREE_B);
  --       b.push_back(:= code >>  6 & 0x3F) | TAG_CONT);
  --       b.push_back(:= code & 0x3F) | TAG_CONT);
  --   } else {
  --       b.push_back(:= code >> 18 & 0x07) | TAG_FOUR_B);
  --       b.push_back(:= code >> 12 & 0x3F) | TAG_CONT);
  --       b.push_back(:= code >>  6 & 0x3F) | TAG_CONT);
  --       b.push_back(:= code & 0x3F) | TAG_CONT);
  --   }

def utf8decode_aux : list char → list char → list char
| p []       := p
| p (c :: r) := utf8decode_aux (p.append (utf8decode_char c)) r

def utf8decode (cb : list char) : list char := utf8decode_aux [] cb
