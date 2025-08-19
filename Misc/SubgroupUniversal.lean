import Mathlib
open CategoryTheory
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

open Grp
variable {G : Grp} (A: Subgroup G)

def i: of A ⟶ G := ofHom {
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
}

def mapsInto : ObjectProperty (Over G) := fun ⟨_, _, f⟩ => f.hom.range ≤ A
def into := FullSubcategory <| mapsInto A
instance : Category (into A) := FullSubcategory.category _
def F: into A ⥤ Grp := fullSubcategoryInclusion _ ⋙ Over.forget _
def Ax : CostructuredArrow (F A) G := @CostructuredArrow.mk _ _ _ _ _ ⟨Over.mk (i A),
  by
    dsimp [mapsInto, Over.mk, CostructuredArrow.mk, i, MonoidHom.range]
    simp only [Subtype.range_coe_subtype]
    exact le_rfl⟩ _ (by
      dsimp
      sorry)
