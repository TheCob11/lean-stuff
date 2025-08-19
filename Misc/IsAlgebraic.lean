import Mathlib
open Polynomial
variable {Z R} [CommRing Z] [Ring R] [Algebra Z R] {x: R}

example : IsAlgebraic Z x ↔ ∃p: Z[X], p ≠ 0 ∧ aeval x p = 0 := Iff.rfl
-- example : IsIntegral Z x ↔ ∃p: Z[X], p.Monic ∧ aeval x p = 0 := Iff.rfl
-- example : Monic p ↔ leadingCoeff p = 1 := Iff.rfl

section Examples
theorem isAlgebraic_sqrt {n: ℕ} [NeZero n] : IsAlgebraic ℤ √n :=
  let p: ℤ[X] := X^2 - (n: ℤ[X])
  have p_nz : p ≠ 0 := X_pow_sub_C_ne_zero zero_lt_two _
  have : aeval √n p = 0 := calc
    _ = aeval √n (X^2) - aeval √n n := map_sub (G := ℤ[X]) (aeval √n) ..
    _ = (√n)^2 - n := congrArg₂ Sub.sub (aeval_X_pow √n) (aeval_C √n _)
    _ = 0 := Real.sq_sqrt n.cast_nonneg |>.substr <| sub_self _
  ⟨p, p_nz, this⟩

end Examples
