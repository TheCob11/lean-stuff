import Mathlib
open Group MulAction Subgroup
open scoped Pointwise
variable [Group G] [act: MulAction G X]

def sigmaFixedEquivSigmaStab : (g: G) × fixedBy X g ≃ (x: X) × stabilizer G x where
  toFun := fun ⟨g, ⟨x, hx⟩⟩ ↦ ⟨x, ⟨g, hx⟩⟩
  invFun := fun ⟨x, ⟨g, hx⟩⟩ ↦ ⟨g, ⟨x, hx⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- #check orbitEquivQuotientStabilizer G ?x |>.symm
-- #check orbitProd
#check selfEquivSigmaOrbits' G X


noncomputable
example : (x: X) × stabilizer G x ≃ G × orbitRel.Quotient G X where
  -- toFun := fun ⟨x, ⟨g, hg⟩⟩ ↦ (groupEquivQuotientProdSubgroup.symm (g, ⟨g, hg⟩), ⟦x⟧)
  toFun := fun ⟨x, ⟨g, hg⟩⟩ ↦ ⟨g, selfEquivSigmaOrbits' G X x |>.fst⟩
  invFun := fun (g, qx) ↦
    ⟨selfEquivSigmaOrbits' G X|>.symm ⟨qx, sorry⟩, groupEquivQuotientProdSubgroup g |>.snd⟩
  -- invFun := fun (g, qx) ↦ ⟨qx.out'⟩
  left_inv := fun ⟨x, ⟨g, hg⟩⟩ ↦ by
    simp only [Sigma.mk.inj_iff]

    sorry
  right_inv := fun ⟨g, qx⟩ ↦ by
    -- refine Prod.ext ?_ (Quotient.out_eq' qx)
    -- simp only [Subtype.coe_eta]
    -- refine Equiv.symm_apply_eq _ |>.mpr ?_

    sorry
