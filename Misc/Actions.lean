import Mathlib

-- A group action is equivalent to a group hom to a permutation group
example [Group G] : (G →* Equiv.Perm α) ≃ MulAction G α where
  toFun φ := {
    smul := fun g a ↦ φ g a
    one_smul := fun _ ↦ by
      simpa only [HSMul.hSMul] using φ.map_one ▸ rfl
    mul_smul := fun g₁ g₂ _ ↦ by
      simpa only [HSMul.hSMul] using φ.map_mul g₁ g₂ ▸ rfl
  }
  invFun _ := {
    toFun := fun g ↦ {
      toFun := (g • ·)
      invFun := (g⁻¹ • ·)
      left_inv := fun _ ↦ inv_smul_eq_iff.mpr rfl
      right_inv := smul_inv_smul g
    }
    map_one' := Equiv.ext <| one_smul G
    map_mul' := fun g₁ g₂ ↦ Equiv.ext <| mul_smul g₁ g₂
  }
  left_inv _ := MonoidHom.ext fun _ ↦ Equiv.ext fun _ ↦ rfl
  right_inv _ := rfl

-- A monoid action is equivalent to a monoid hom to an endomorphism monoid
example [Monoid M] : (M →* Function.End α) ≃ MulAction M α where
  toFun φ := {
    smul := fun m ↦ φ m
    one_smul := fun _ ↦ by
      simpa only [HSMul.hSMul] using φ.map_one ▸ rfl
    mul_smul := fun m₁ m₂ _ ↦ by
      simpa only [HSMul.hSMul] using φ.map_mul m₁ m₂ ▸ rfl
  }
  invFun inst := {
    toFun := inst.smul
    map_one' := funext <| inst.one_smul
    map_mul' := fun m₁ m₂ ↦ funext <| inst.mul_smul m₁ m₂
  }
  left_inv φ := rfl
  right_inv inst := rfl

-- A module (ring action!) is equivalent to a ring hom to an endomorphism ring
example [Semiring R] [AddCommMonoid M] : (R →+* AddMonoid.End M) ≃ Module R M where
    toFun φ := {
      smul := fun r ↦ φ r
      one_smul := fun _ ↦ by
        simpa only [HSMul.hSMul] using φ.map_one ▸ rfl
      zero_smul := fun _ ↦ by
        simpa only [HSMul.hSMul] using φ.map_zero ▸ rfl
      mul_smul := fun r₁ r₂ _ ↦ by
        simpa only [HSMul.hSMul] using φ.map_mul r₁ r₂ ▸ rfl
      add_smul := fun r₁ r₂ m ↦ by
        simpa only [HSMul.hSMul] using φ.map_add r₁ r₂ ▸ rfl
      smul_zero := fun r ↦ (φ r).map_zero
      smul_add := fun r m₁ m₂ ↦ (φ r).map_add m₁ m₂
    }
    invFun inst := {
      toFun := fun r ↦ {
        toFun := inst.smul r
        map_zero' := inst.smul_zero r
        map_add' := inst.smul_add r
      }
      map_one' := AddMonoidHom.ext <| inst.one_smul
      map_zero' := AddMonoidHom.ext <| inst.zero_smul
      map_mul' := fun r₁ r₂ ↦ AddMonoidHom.ext <| inst.mul_smul r₁ r₂
      map_add' := fun r₁ r₂ ↦ AddMonoidHom.ext <| inst.add_smul r₁ r₂
    }
    left_inv _ := rfl
    right_inv _ := rfl
