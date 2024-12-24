import Mathlib

-- #eval
--   let x: ℚ := -1/0
--   (-1/(x.den + 1)) < x
--   -- x < (1/(x.den + 1))
def S: Set (Set ℚ) := {Set.Ioo (-((n: ℚ)⁻¹)) n⁻¹ | (n : ℕ) (_: 0 < n)}

namespace S

theorem all_open : s ∈ S → IsOpen s := fun ⟨_, _, h⟩ ↦ h.subst isOpen_Ioo

example (x: ℝ) : Filter.atTop.Tendsto (fun n: ℕ ↦ (n: ℝ)⁻¹) (nhds 0) := by
  simp [nhds]
  intros S zero_mem hS
  -- #check isOpen_iff_generate_intervals.mp hS
  use 0
  rintro n -
  induction n
  next => simpa only [CharP.cast_eq_zero, inv_zero] using zero_mem
  next n hn =>
  let ⟨ε, ⟨ε_pos, hε⟩⟩ := Metric.isOpen_iff.mp hS _ hn
  simp [Metric.ball] at hε


  sorry

example (x : ℝ) (h: ∀ (a: ℕ), 0 < a → -(↑a)⁻¹ < x ∧ x < (↑a)⁻¹) : x = 0 := by

  sorry

lemma Rat.divInt_one_succ (n: ℕ) : let x := Rat.divInt 1 (n + 1)
  x.num = 1 ∧ x.den = n + 1 := by
  simp [Rat.divInt]
  split
  next hd =>
    simp [mkRat, Rat.normalize]
    split
    next h => exact absurd hd <| h ▸ n.cast_add_one_ne_zero
    next h => simp only [Int.ofNat_eq_coe, true_and] at h hd ⊢; exact_mod_cast hd.symm
  next heq => exact Int.noConfusion heq

example (x : ℚ) (h: ∀ (a: ℕ), 0 < a → -(↑a)⁻¹ < x ∧ x < (↑a)⁻¹) : x = 0 :=
  by_contra fun hx ↦ by
  have squeeze := h (x.den + 1) x.den.succ_pos
  let y : ℚ := ⟨1, x.den + 1, x.den.add_one_ne_zero, Nat.coprime_one_left _⟩
  have : ((x.den + 1) : ℚ)⁻¹ = y :=
    have ⟨num_eq, den_eq⟩ := Rat.divInt_one_succ x.den
    mod_cast Rat.inv_def' _ |>.trans <| Rat.ext num_eq den_eq
  simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, this] at squeeze

  sorry

-- this was much more complicated than i was expecting
lemma squeeze (x : ℚ) (h: ∀ (a: ℕ), 0 < a → -(↑a)⁻¹ < x ∧ x < (↑a)⁻¹) : x = 0 :=
  by_contra fun hx ↦ by
  have squeeze := h (x.den + 1) x.den.succ_pos
  let y : ℚ := ⟨1, x.den + 1, x.den.add_one_ne_zero, Nat.coprime_one_left _⟩
  have : ((x.den + 1) : ℚ)⁻¹ = y :=
    have ⟨num_eq, den_eq⟩ := Rat.divInt_one_succ x.den
    mod_cast Rat.inv_def' _ |>.trans <| Rat.ext num_eq den_eq
  simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, this] at squeeze
  match Ne.lt_or_lt hx with
  | .inl x_neg =>
    absurd squeeze.left
    simp [Rat.le_def]
    have ⟨nN, hnN⟩ := Int.eq_negSucc_of_lt_zero <| Rat.num_neg.mpr x_neg
    simp [hnN, Int.le_def, Int.nonneg_def, Int.negSucc_coe]
    ring_nf
    exact ⟨_, rfl⟩
  | .inr x_pos =>
    absurd squeeze.right
    simp [Rat.le_def]
    have ⟨nN, hnN⟩ := Int.eq_succ_of_zero_lt <| Rat.num_pos.mpr x_pos
    simp [hnN]
    norm_cast
    ring_nf
    exact x.den.le_add_left _

theorem sInter_eq_singleton_zero : ⋂₀ S = {0} := by
  dsimp only [Set.sInter, sInf]
  refine Set.ext fun x ↦ ?_
  simp only [Set.mem_setOf_eq, forall_exists_index,
             forall_apply_eq_imp_iff₂, Set.mem_Ioo, S]
  exact Iff.intro (squeeze x) fun hx n hn ↦ by
    subst hx
    simpa only [inv_lt_zero, Left.neg_neg_iff, Nat.cast_pos, inv_pos, and_self]

theorem not_open_sInter : ¬IsOpen (⋂₀ S) :=
  sInter_eq_singleton_zero.substr <| not_isOpen_singleton 0

end S

example : ∃ (X: Type) (_: TopologicalSpace X) (S: Set (Set X))
  (_: ∀s∈S, IsOpen s),  ¬IsOpen (⋂₀ S) := ⟨_, _, S, @S.all_open, S.not_open_sInter⟩
