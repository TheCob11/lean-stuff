import Mathlib
open Real

def G: Type := {x: ℝ // x ≠ -1}

-- # Problem: show that G forms a group under ⟨a, _⟩ * ⟨b, _⟩ = a + b + a * b

/- note: a lot of these proofs can be done easier w/sprawling simp tactics like ring and linarith,
I'm mostly avoiding them but sometimes I don't when stuff is sufficiently trivial + annoying -/

theorem add_add_mul_eq {a b : ℝ} : a + b + a * b = (a + 1) * (b + 1) - 1 := Eq.symm <| calc
  _ = a * b + 1 * b + (a * 1 + 1 * 1) - 1 := by rw [left_distrib, right_distrib, right_distrib]
  _ = a * b + b + (a + 1) - 1 := by rw [mul_one, one_mul, one_mul]
  _ = a + b + a * b := by abel

instance : Mul G := .mk fun
  | ⟨a, ha⟩, ⟨b, hb⟩ => .mk (a + b + a * b) <| add_add_mul_eq.substr fun h ↦
    have : (a + 1) * (b + 1) = 0 := sub_eq_neg_self.mp h
    have : a + 1 = 0 ∨ b + 1 = 0 := mul_eq_zero.mp this
    have : a = -1 ∨ b = -1 := this.imp add_eq_zero_iff_eq_neg.mp add_eq_zero_iff_eq_neg.mp
    this.elim ha hb

example {a b: ℝ} (h: a + b + a * b = 0) : b = (a + 1)⁻¹ - 1 :=
  have : (a + 1) * (b + 1) - 1 = 0 := add_add_mul_eq ▸ h
  have : (a + 1) * (b + 1) = 1 := sub_eq_zero.mp this
  have : b + 1 = (a + 1)⁻¹ := DivisionMonoid.inv_eq_of_mul (a + 1) (b + 1) this |>.symm
  eq_sub_of_add_eq this

noncomputable
instance : Inv G := .mk fun ⟨a, ha⟩ ↦ .mk ((a + 1)⁻¹ - 1) <| fun h ↦
  have : (a + 1)⁻¹ = 0 := sub_eq_neg_self.mp h
  have : a + 1 = 0 := inv_eq_zero.mp this
  add_eq_zero_iff_eq_neg.not.mpr ha this

instance : One G := ⟨⟨0, by simp⟩⟩

noncomputable
instance : Group G := .ofLeftAxioms
  (fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ↦ Subtype.ext <| by
    change a + b + a * b + c + (a + b + a * b) * c = a + (b + c + b * c) + a * (b + c + b * c)
    ring)
  (fun ⟨a, _⟩ ↦ Subtype.ext <| zero_add a |>.subst <| add_right_eq_self.mpr <| zero_mul a)
  fun ⟨g, hg⟩ ↦ Subtype.ext <| by
    change (g + 1)⁻¹ - 1 + g + ((g + 1)⁻¹ -1) * g = 0
    suffices -1 + g * (1 + g)⁻¹ + (1 + g)⁻¹ = 0 by ring_nf; exact this
    suffices g * (1 + g)⁻¹ + (1 + g)⁻¹ + -1 = 0 by linarith
    suffices g * (1 + g)⁻¹ + (1 + g)⁻¹ = 1 from add_neg_eq_zero.mpr this
    suffices (1 + g) * (1 + g)⁻¹ = 1 from calc
      _ = (1 + g)⁻¹ + g * (1 + g)⁻¹ := add_comm _ _
      _ = 1 * (1 + g)⁻¹ + g * (1 + g)⁻¹ := by rw [one_mul]
      _ = (1 + g) * (1 + g)⁻¹ := right_distrib .. |>.symm
      _ = 1 := this
    have : 1 + g ≠ 0 := add_eq_zero_iff_neg_eq.not.mpr hg.symm
    exact mul_inv_cancel this
