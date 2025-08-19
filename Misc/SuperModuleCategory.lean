import Mathlib
open CategoryTheory
local notation:80 f " ⊚ " g => CategoryStruct.comp g f

structure SuperModCat where
  R : Type _
  [isRing : Ring R]
  carrier : Type _
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]

attribute [instance] SuperModCat.isRing SuperModCat.isAddCommGroup SuperModCat.isModule

instance [Semiring R₁] [Semiring R₂] [Semiring R₃] (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) :
  RingHomCompTriple σ₁₂ σ₂₃ (σ₂₃.comp σ₁₂) := ⟨rfl⟩

namespace SuperModCat

structure Hom (M N : SuperModCat) where
  {σ : M.R →+* N.R}
  hom : M.carrier →ₛₗ[σ] N.carrier

instance : Category SuperModCat where
  Hom := Hom
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom.comp f.hom⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
