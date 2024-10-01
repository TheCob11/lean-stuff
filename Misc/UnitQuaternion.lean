import Mathlib
open Quaternion
theorem Quaternion.sq_eq_neg_one_iff_re_zero_and_norm_1 (q: ℍ) :
  q ^ 2 = -1 ↔ q.re = 0 ∧ normSq q = 1 :=
  have mp (h: q ^ 2 = -1) : q.re = 0 ∧ normSq q = 1 :=
    have left : q.re = 0 := by_contra fun hr_nz ↦ by
      have hr := Quaternion.mul_re q q
      have hi := Quaternion.mul_imI q q
      have hj := Quaternion.mul_imJ q q
      have hk := Quaternion.mul_imK q q
      simp [↓←sq, h] at hr hi hj hk
      ring_nf at hr hi hj hk
      rw [mul_assoc, mul_comm, mul_assoc, mul_comm] at hi hj hk
      set re2 := 2*q.re
      have re2_nz : re2 ≠ 0 := mul_ne_zero two_ne_zero hr_nz
      have iz : q.imI = 0 := zero_eq_mul.mp hi |>.resolve_left re2_nz
      have jz : q.imJ = 0 := zero_eq_mul.mp hj |>.resolve_left re2_nz
      have kz : q.imK = 0 := zero_eq_mul.mp hk |>.resolve_left re2_nz
      simp [iz, jz, kz] at hr
      exact absurd hr (neg_one_lt_zero.trans <| sq_pos_of_ne_zero hr_nz).ne
    have right : normSq q = 1 := by
      have : -(q ^ 2) = (1: ℝ) := neg_eq_iff_eq_neg.mpr h
      rw [← Quaternion.coe_inj, ← this, ← neg_eq_iff_eq_neg]
      exact sq_eq_neg_normSq.mpr left |>.symm
    ⟨left, right⟩
  have mpr (h: q.re = 0 ∧ normSq q = 1) : q ^ 2 = -1 :=
    sq_eq_neg_normSq.mpr h.left ▸ h.right ▸ rfl
  ⟨mp, mpr⟩

example : {q : ℍ | q ^ 2 = -1} =
  {⟨re, ii, ij, ik⟩: ℍ | re = 0 ∧ ii^2 + ij^2 + ik^2 = 1} := Set.ext fun x ↦
  sq_eq_neg_one_iff_re_zero_and_norm_1 x |>.trans <| and_congr_right fun h ↦
    @normSq_def' ℝ _ x ▸ h ▸
      (@zero_pow ℝ _ 2 two_ne_zero).symm ▸ @zero_add ℝ _ _ ▸ Iff.rfl
