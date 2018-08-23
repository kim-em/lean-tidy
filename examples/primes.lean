import data.nat.prime

open nat



theorem exists_infinite_primes : ∀ n : ℕ, ∃ p, p ≥ n ∧ prime p :=
λ n,
  let p := min_fac (fact n + 1) in
  have fp : fact n > 0 := fact_pos n,
  have f1 : fact n + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ fact_pos n,
  have pp : prime p, from min_fac_prime f1,
  have w : n ≤ p, from le_of_not_ge $ λ h,
    have h₁ : p ∣ fact n, from dvd_fact (min_fac_pos (fact n + 1)) h,
    have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd (fact n + 1)),
    pp.not_dvd_one h₂,
  ⟨p, w, pp⟩