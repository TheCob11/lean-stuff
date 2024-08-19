import Mathlib

theorem nrt_prime_irrational {n: ℕ} [n.AtLeastTwo] (p: ℕ) (hp: Nat.Prime p) {s: ℝ} (hs: s ^ n = p) : Irrational s := by
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
  let pZ : ℤ := ↑p;
  have pZ_dvd_pow {m: ℤ} (h : pZ ∣ m ^ n) := Int.Prime.dvd_pow' hp h;
  have pZ_dvd_a : pZ ∣ a := pZ_dvd_pow ⟨(↑b ^ n), h.symm⟩
  have p_dvd_b : p ∣ b :=
    have pZ_dvd_bZ_n : pZ ∣ (↑b) ^ n :=
      have n_nz : n ≠ 0 := (NeZero.ne' n).symm;
      have n_m1_nz : n - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr Nat.AtLeastTwo.one_lt;
      have pZ_pos : 0 < pZ := Int.ofNat_pos.mpr hp.pos;
      let factor := p ^ (n-2) * pZ_dvd_a.choose ^ n;
      have : b^n = pZ * factor := by
        rwa [pZ_dvd_a.choose_spec, mul_pow,
             ← mul_pow_sub_one n_nz pZ, ← mul_pow_sub_one n_m1_nz pZ,
             mul_assoc, mul_left_cancel_iff_of_pos pZ_pos, mul_assoc] at h
      ⟨factor, this⟩
    Int.ofNat_dvd.mp (pZ_dvd_pow pZ_dvd_bZ_n)
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, Int.ofNat_dvd_left.mp pZ_dvd_a, p_dvd_b⟩ reduced

example {n: ℕ} [n.AtLeastTwo] {s: ℝ} (hs: s ^ n = 2) : Irrational s := nrt_prime_irrational 2 Nat.prime_two hs
example : Irrational √2 := nrt_prime_irrational 2 Nat.prime_two (Real.sq_sqrt zero_le_two)
