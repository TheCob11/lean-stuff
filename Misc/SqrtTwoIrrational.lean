import mathlib
lemma even_sq {a: ℤ} (h: Even (a^2)) : Even a := by
  rwa [Int.even_pow' (Ne.symm (Nat.zero_ne_add_one 1))] at h
theorem sqrt_two_irrational : Irrational √2 := by
  rw [irrational_iff_ne_rational]
  intro a1 b1
  by_contra h
  let x := Rat.divInt a1 b1;
  let a := x.num; let b := x.den;
  replace h : √2 = ↑x := by rwa [← Rat.cast_mk] at h;
  have a_pos : 0 < a := by
    have a_nonneg : 0 ≤ a := by
      by_contra h2
      rw [Int.not_le, Rat.num_neg, ←Real.ratCast_lt, ←h] at h2
      absurd h2
      rw [Rat.cast_zero]; push_neg;
      exact Real.sqrt_nonneg 2
    have a_nz : 0 ≠ a := by
      by_contra h2
      absurd h
      replace h2 := h2.symm;
      rw [Rat.num_eq_zero] at h2;
      rw [h2]; simp;
    exact lt_of_le_of_ne a_nonneg a_nz
  have xR_nonneg : 0 ≤ (x:ℝ) := by simp_rw [←h, Real.sqrt_nonneg 2];
  rw [Real.sqrt_eq_iff_sq_eq (zero_le_two) xR_nonneg] at h
  norm_cast at h
  rw [Rat.eq_iff_mul_eq_mul] at h; simp at h;
  have a_even : Even a := even_sq (by simp_all only [even_two, Even.mul_right])
  have aN_even : Even a.natAbs := Int.natAbs_even.mpr a_even;
  have b_even : Even b := by
    have bZ_even := even_sq (by
      use a_even.choose ^ 2;
      have k_spec := a_even.choose_spec;
      unfold_let a at k_spec
      rw [k_spec, ← Int.two_mul, mul_pow, sq, Int.mul_assoc] at h;
      have two_pos : 0 < (2: ℤ) := (Int.sign_eq_one_iff_pos 2).mp rfl
      rw [mul_left_cancel_iff_of_pos two_pos, two_mul] at h;
      exact h.symm)
    rwa [Int.even_coe_nat b] at bZ_even
  absurd x.reduced
  rw [Nat.Prime.not_coprime_iff_dvd]
  use 2
  apply And.intro; trivial; apply And.intro
  · exact even_iff_two_dvd.mp aN_even
  · exact even_iff_two_dvd.mp b_even
