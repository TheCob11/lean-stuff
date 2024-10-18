import Mathlib
open Polynomial Complex
noncomputable section

abbrev C2.J : Ideal ℝ[X] := .span { X^2 + 1 }
abbrev C2 := ℝ[X] ⧸ C2.J
namespace C2
open Ideal.Quotient
instance : CommRing C2 := commRing C2.J
theorem mk_X_sq_eq_neg_one : mk J X * mk J X = -1 := (sq _).symm.trans <|
  mk_eq_mk_iff_sub_mem .. |>.mpr <| sub_neg_eq_add (α := ℝ[X]) .. ▸
    Ideal.mem_span_singleton_self _
def I' : {I' : C2 // I' * I' = -1} := ⟨mk J X, mk_X_sq_eq_neg_one⟩
example : ℝ[X] →ₐ[ℝ] ℂ := aevalTower ofRealAm I
example : ℂ →ₐ[ℝ] C2 := Complex.lift I'
theorem eval₂_ofReal_I_mem_J_eq_zero x (h: x ∈ J): eval₂ ofReal I x = 0 := by
  let ⟨_k, hk⟩ := Ideal.mem_span_singleton'.mp h
  simp [← hk, eval₂_mul, eval₂_add, eval₂_X_pow,
        I_sq, eval₂_one, add_left_neg, mul_zero]
def toCAlgHom : C2 →ₐ[ℝ] ℂ := liftₐ C2.J (aevalTower ofRealAm I)
  eval₂_ofReal_I_mem_J_eq_zero

def toCAlgEquiv : C2 ≃ₐ[ℝ] ℂ := AlgEquiv.ofAlgHom toCAlgHom (Complex.lift I') |> And.elim <| by
  refine And.intro (AlgHom.ext fun z ↦ ?_) (AlgHom.ext fun x ↦ ?_)
  ·
    -- simp [toCAlgHom, I', algebraMap, Algebra.toRingHom]
    sorry
  · -- simp
    dsimp only [AlgHom.coe_comp, Function.comp_apply, liftAux_apply, AlgHom.coe_id,
      id_eq, algebraMap, Algebra.toRingHom, Ideal.Quotient.mk, toCAlgHom]
    simp [algebraMap, Algebra.toRingHom]
    simp [aevalTower]
    -- set_option maxHeartbeats 0 in rw?
    -- simp [Complex.lift, algebraMap, Algebra.toRingHom, I', toCAlgHom, aevalTower]
    sorry

-- example : C2 ≃ ℂ where
--   toFun x := Ideal.Quotient.lift C2_Ideal (mapRingHom ofReal) (sorry) x |>.eval 1
--   invFun z := ofFinsupp [z.re, z.im].toFinsupp
--   left_inv _ := by
--     simp []
--   right_inv := sorry
