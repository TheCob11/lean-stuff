import Mathlib

theorem nrt_two_irrational {n: ℕ} [n.AtLeastTwo] {s: ℝ} (hs: s ^ n = 2): Irrational s := by
  rw [irrational_iff_ne_rational]
  intro a1 b1
  by_contra h
  rw [← Rat.cast_mk] at h
  let x := Rat.divInt a1 b1;
  replace h : s ^ n = ↑x ^ n := by tauto
  obtain ⟨a, b, _b_nz, reduced⟩ := x;
  rw [hs] at h
  norm_cast at h
  simp [Rat.eq_iff_mul_eq_mul] at h;
  have n_nz : n ≠ 0 := (NeZero.ne' n).symm
  have even_pow_n {m: ℤ} : Even (m ^ n) → Even m := (Int.even_pow' n_nz).mp
  have a_even : Even a := even_pow_n ⟨b ^ n, Eq.symm (by rwa [two_mul] at h)⟩
  have aN_even : Even a.natAbs := Int.natAbs_even.mpr a_even
  have b_even : Even b :=
    have bZ_pow_n_even : Even ((b: ℤ) ^ n) := by
      have k_spec := a_even.choose_spec;
      unfold_let a at k_spec
      rw [k_spec, ← two_mul, mul_pow] at h;
      rw [← mul_pow_sub_one n_nz 2, ← mul_pow_sub_one (Nat.sub_ne_zero_iff_lt.mpr Nat.AtLeastTwo.one_lt) 2] at h
      rw [mul_assoc, mul_left_cancel_iff_of_pos zero_lt_two, mul_assoc, two_mul] at h
      exact ⟨(2 ^ (n-2)) * a_even.choose ^ n, h⟩
    have bZ_even : Even (b: ℤ) := even_pow_n bZ_pow_n_even;
    (Int.even_coe_nat b).mp bZ_even
  absurd reduced
  rw [Nat.Prime.not_coprime_iff_dvd]; use 2
  rw [← even_iff_two_dvd, ← even_iff_two_dvd]
  exact ⟨Nat.prime_two, aN_even, b_even⟩

example : Irrational √2 := nrt_two_irrational (Real.sq_sqrt zero_le_two)
