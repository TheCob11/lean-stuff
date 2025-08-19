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
-- #check selfEquivSigmaOrbits' G X

example [Fintype G] [Fintype X] : ∑g: G, Nat.card (fixedBy X g) =
                      Nat.card (orbitRel.Quotient G X) * Nat.card G := calc
  ∑g: G, Nat.card (fixedBy X g)
  _ = ∑x: X, Nat.card (stabilizer G x) := by
    refine
      Function.Bijective.finset_sum ?e ?he (fun x ↦ Nat.card ↑(fixedBy X x))
        (fun x ↦ Nat.card ↥(stabilizer G x)) ?h
    sorry
    sorry
    sorry
  _ = _ := sorry

noncomputable
example : (x: X) × stabilizer G x ≃ G × orbitRel.Quotient G X where
  -- toFun := fun ⟨x, ⟨g, hg⟩⟩ ↦ (groupEquivQuotientProdSubgroup.symm (g, ⟨g, hg⟩), ⟦x⟧)
  toFun := fun ⟨x, ⟨g, hg⟩⟩ ↦ (g, selfEquivSigmaOrbits' G X x |>.fst)
  -- invFun := fun (g, qx) ↦
  --   ⟨selfEquivSigmaOrbits' G X|>.symm ⟨qx, ⟨qx.out', sorry⟩⟩, groupEquivQuotientProdSubgroup g |>.snd⟩
  invFun := fun (g, qx) ↦ ⟨qx.out', groupEquivQuotientProdSubgroup g |>.snd⟩
  left_inv := fun ⟨x, ⟨g, (hg: g • x = x)⟩⟩ ↦ by
    simp only [Sigma.mk.inj_iff]
    apply And.intro
    ·
      sorry
    ·
      sorry
  right_inv := fun ⟨g, qx⟩ ↦ by
    -- refine Prod.ext ?_ (Quotient.out_eq' qx)
    -- simp only [Subtype.coe_eta]
    -- refine Equiv.symm_apply_eq _ |>.mpr ?_

    sorry
