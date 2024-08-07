import mathlib
open Nat
theorem infinite_primes : Infinite Primes := by
  rw [Primes, ← Set.coe_setOf, Set.infinite_coe_iff, Set.infinite_iff_exists_gt]
  intro n
  let m := n ! + 1
  let p := minFac m;
  have p_prime : Nat.Prime p := by
    have m_ne_1 : m ≠ 1 := add_left_ne_self.mpr (factorial_ne_zero n);
    exact minFac_prime m_ne_1
  -- wow this would also work
  -- have p_prime : Nat.Prime p := minFac_prime <| add_left_ne_self.mpr <| factorial_ne_zero n;
  have n_lt_p : n < p := by
    rw [lt_iff_not_le, ← p_prime.dvd_factorial]
    by_contra h
    absurd p_prime.not_dvd_one
    rw [Nat.dvd_add_iff_right h]
    exact minFac_dvd m
  exact ⟨p, p_prime, n_lt_p⟩
  -- also could be
  -- exact ⟨p, ‹p.Prime›, ‹n < p›⟩
