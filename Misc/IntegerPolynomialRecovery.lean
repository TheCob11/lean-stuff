import Mathlib

open Polynomial Nat

def solve (f1 ff1p1 : ℕ) : ℕ[X] := .ofFinsupp <|
  (f1 + 1).digits ff1p1 |>.toFinsupp

#eval do
  let (a, b, c) := (0, 1, 0)
  -- let a ← IO.rand 0 100
  -- let b ← IO.rand 0 100
  -- let c ← IO.rand 0 100
  let f : ℕ[X] := .ofFinsupp [a, b, c].toFinsupp
  println! repr f
  let f1 := f.eval 1
  let ff1p1 := f.eval (f1 + 1)
  println! (f1, ff1p1)
  let g := solve f1 ff1p1
  println! repr g
  println! (g.eval 1, g.eval (f1 + 1))

def Polynomial.coeffList [Semiring R] (self: R[X]) : List R :=
  .ofFn (n := self.degree.elim 0 succ) (self.coeff ·)

-- #eval @Polynomial.coeffList ℕ _ (.ofFinsupp [0].toFinsupp)

theorem Polynomial.coeff_list_index [Semiring R] (self: R[X]) :
  self.coeff n = self.coeffList.getD n 0 := if h_deg_bot: self.degree = ⊥
  then degree_eq_bot.mp h_deg_bot ▸ rfl
  else by
  let hdeg := Option.ne_none_iff_exists'.mp h_deg_bot |>.choose_spec
  unfold coeffList
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.ofFnNthVal]
  split
  next => exact rfl
  next h => exact hdeg ▸ self.coeff_eq_zero_of_degree_lt <| cast_lt.mpr <|
    not_lt.mp <| hdeg ▸ h

-- example (f: ℕ[X]) : f.eval = Nat.ofDigits (f.eval 1 + 1) f.toFinsupp := sorry

example (f: ℕ[X]) (f1 ff1p1: ℕ) (hf: f.eval 1 = f1 ∧ f.eval (f1 + 1) = ff1p1) :
  solve f1 ff1p1 = f := Polynomial.ext fun n ↦ by
  obtain ⟨hf1, hff1p1⟩ := hf
  simp [solve]
  induction n
  · rw [coeff_zero_eq_eval_zero, Option.getD]
    split
    next _ x h =>
      rename_i opt
      rw [@List.getElem?_eq_some] at h
      obtain ⟨h_len, h⟩ := h
      -- rw [digits_def'] at h
      sorry
    next _ h =>
      rename_i opt
      simp_all only [List.getElem?_eq_none_iff, nonpos_iff_eq_zero, List.length_eq_zero]
      sorry
  · sorry

-- example (f1 ff1p1 : ℕ) (hf1: f1 ≠ 1):
--   let f := solve f1 ff1p1;
--   f.eval 1 = f1 ∧ f.eval (f.eval 1 + 1) = ff1p1 := by
--   intro coeffs f
--   dsimp [f]
--   rw [mul_one, mul_one]
--   have := Nat.modEq_digits_sum f1 (f1 + 1) (Nat.add_mod_left _ _ |>.symm ▸ Nat.one_mod_of_ne_one hf1) ff1p1
--   apply And.intro
--   · simp [coeffs, getCoeffs]
--     sorry
--   · sorry

-- example (f1 ff1 : ℕ) : ∃(a b c : ℕ), (let f x := a * x ^ 2 + b * x + c; f 1 = f1 ∧ f (f 1) = ff1) :=
--   let base := f1 + 1
--   let gurg := (base.digits ff1).rightpad 3 0
--   let (a, b, c) := (gurg[1]!, gurg[2]!, gurg[3]!)
--   by
--   use a, b, c
--   intro f
--   aesop
--   -- #check digits_sum
--   sorry
-- -- #eval (6).digits 15
