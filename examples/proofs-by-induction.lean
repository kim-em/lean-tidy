import algebra.big_operators data.fintype
import tactic.ring
import tidy.tidy

-- https://xenaproject.wordpress.com/2018/03/30/proofs-by-induction/

open nat

def odd : ℕ → ℕ := λ i, 2 * i + 1
def square : ℕ → ℕ := λ i, i ^ 2
@[ematch] theorem odd_square_inductive_step (d : ℕ) :
  square d + odd d = square (succ d) :=
begin dsimp [square, odd], rw [succ_eq_add_one], ring, sorry end

namespace def1

definition my_sum_to_n (summand : ℕ → ℕ) : ℕ → ℕ
| 0 := 0
| (succ n) := my_sum_to_n n + summand n

theorem my_zero_theorem (summand : ℕ → ℕ) :
  my_sum_to_n summand 0 = 0 :=
rfl

theorem my_successor_theorem (summand : ℕ → ℕ) (n : ℕ) :
  my_sum_to_n summand (succ n) = my_sum_to_n summand n + summand n :=
by obviously

lemma foo : 3 + 4 = 7 := 
begin
 dsimp', -- I'd really like dsimp' to not muck + up like this.
end

theorem my_odd_square_theorem : ∀ (n : ℕ), my_sum_to_n odd n = square n
| 0        := rfl
| (succ n) := begin unfold my_sum_to_n, obviously, rw [my_odd_square_theorem n], exact odd_square_inductive_step n, end

end def1

namespace def2

definition my_sum_to_n (summand : ℕ → ℕ) : ℕ → ℕ :=
λ n, ((list.range n).map summand).sum

theorem my_zero_theorem (summand : ℕ → ℕ) :
  my_sum_to_n summand 0 = 0 :=
rfl

theorem my_successor_theorem (summand : ℕ → ℕ) (n : ℕ) :
  my_sum_to_n summand (succ n) = my_sum_to_n summand n + summand n :=
by unfold my_sum_to_n; simp [list.range_concat]

theorem my_odd_square_theorem : ∀ (n : ℕ), my_sum_to_n odd n = square n
| 0        := rfl
| (succ n) := by rw [my_successor_theorem, my_odd_square_theorem n]; exact odd_square_inductive_step n

end def2

namespace def3

definition my_sum_to_n (summand : ℕ → ℕ) : ℕ → ℕ :=
λ n, (finset.range n).sum summand

theorem my_zero_theorem (summand : ℕ → ℕ) :
  my_sum_to_n summand 0 = 0 :=
rfl

theorem my_successor_theorem (summand : ℕ → ℕ) (n : ℕ) :
  my_sum_to_n summand (succ n) = my_sum_to_n summand n + summand n :=
by unfold my_sum_to_n; simp

theorem my_odd_square_theorem : ∀ (n : ℕ), my_sum_to_n odd n = square n
| 0        := rfl
| (succ n) := by rw [my_successor_theorem, my_odd_square_theorem n]; exact odd_square_inductive_step n

end def3

namespace def4

open finset nat

-- Credits to Chris Hughes
theorem chris (n : ℕ) (f : ℕ → ℕ) (g : fin n → ℕ) (h : ∀ i : fin n, f i.1  = g i) :
    (range n).sum f = univ.sum g :=
sum_bij
  (λ i h, ⟨i, mem_range.1 h⟩)
  (λ i h, mem_univ _)
  (λ a ha, h ⟨a, _⟩)
  (λ _ _ _ _, fin.veq_of_eq)
  (λ ⟨b, hb⟩ _, ⟨b, mem_range.2 hb, rfl⟩)

definition my_sum_to_n (summand : ℕ → ℕ) : ℕ → ℕ :=
λ n, (@finset.univ (fin n) _).sum (summand ∘ fin.val)

theorem my_zero_theorem (summand : ℕ → ℕ) :
  my_sum_to_n summand 0 = 0 :=
rfl

-- Credits to Mario Carneiro
theorem my_successor_theorem (summand : ℕ → ℕ) (n : ℕ) :
  my_sum_to_n summand (succ n) = my_sum_to_n summand n + summand n :=
by unfold my_sum_to_n;
rw [← chris _ _ _ (λ _, rfl), ← chris _ _ _ (λ _, rfl)]; simp

theorem my_odd_square_theorem : ∀ (n : ℕ), my_sum_to_n odd n = square n
| 0        := rfl
| (succ n) := by rw [my_successor_theorem, my_odd_square_theorem n]; exact odd_square_inductive_step n

end def4

namespace equality

theorem def12 : def1.my_sum_to_n = def2.my_sum_to_n :=
funext $ λ summand, funext $ λ n, nat.rec_on n rfl $
λ m ih, by rw [def1.my_successor_theorem, def2.my_successor_theorem, ih]

theorem def23 : def2.my_sum_to_n = def3.my_sum_to_n :=
funext $ λ summand, funext $ λ n, nat.rec_on n rfl $
λ m ih, by rw [def2.my_successor_theorem, def3.my_successor_theorem, ih]

theorem def34 : def3.my_sum_to_n = def4.my_sum_to_n :=
funext $ λ summand, funext $ λ n, nat.rec_on n rfl $
λ m ih, by rw [def3.my_successor_theorem, def4.my_successor_theorem, ih]

end equality