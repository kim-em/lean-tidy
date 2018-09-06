import data.nat.basic
import data.pnat
import tactic.norm_num

lemma nat.succ_pred (n : ℕ) (h : n ≠ 0) : nat.succ (nat.pred n) = n :=
begin
  cases n,
  contradiction,
  simp
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
  simp
end

lemma fin.with_max' (n : ℕ) (m : pnat) : fin m :=
⟨ min n (m-1), begin
                 have p := min_le_right n (nat.pred m),
                 have q := nat.lt_succ_of_le p,
                 rw nat.succ_pred at q,
                 exact q,
                 exact nat.pos_iff_ne_zero.mp m.property,
               end ⟩

def nat.trunc_to_char (n : nat) : char :=
if h : n > 255 then ⟨ 255, begin unfold is_valid_char, norm_num end ⟩ else ⟨ n, begin unfold is_valid_char, simp at h, left, transitivity 256, apply nat.lt_succ_of_le, assumption, norm_num end ⟩