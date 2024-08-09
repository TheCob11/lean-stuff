import Mathlib
lemma even_sq {a: ℤ} (h: Even (a^2)) : Even a := (Int.even_pow' two_ne_zero).mp h
theorem sqrt_two_irrational : Irrational √2 := by
  rw [irrational_iff_ne_rational];
  intro a1 b1;
  by_contra h;
  let x := Rat.divInt a1 b1;
  let a := x.num; let b := x.den;
  replace h : √2 = ↑x := by rwa [← Rat.cast_mk] at h;
  have xR_nonneg : 0 ≤ (x:ℝ) := by simp_rw [← h, Real.sqrt_nonneg 2];
  rw [Real.sqrt_eq_iff_sq_eq zero_le_two xR_nonneg] at h
  norm_cast at h
  simp [Rat.eq_iff_mul_eq_mul] at h;
  have a_even : Even a := even_sq (by simp_all only [even_two, Even.mul_right])
  have aN_even : Even a.natAbs := Int.natAbs_even.mpr a_even;
  have b_even : Even b := by
    have bZ_even : Even (b: ℤ) := even_sq (by
      use a_even.choose ^ 2;
      have k_spec := a_even.choose_spec;
      unfold_let a at k_spec
      rw [k_spec, ← two_mul, mul_pow, sq, mul_assoc] at h;
      rw [mul_left_cancel_iff_of_pos zero_lt_two, two_mul] at h;
      exact h.symm)
    exact (Int.even_coe_nat b).mp bZ_even
  absurd x.reduced
  rw [Nat.Prime.not_coprime_iff_dvd]; use 2
  rw [← even_iff_two_dvd, ← even_iff_two_dvd]
  exact ⟨Nat.prime_two, aN_even, b_even⟩
