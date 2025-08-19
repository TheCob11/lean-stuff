import Mathlib
open CategoryTheory MonoidalCategory

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

instance [Preorder α] [AddMonoid α] [AddLeftMono α] [AddRightMono α] : MonoidalCategory α where
  tensorObj x y := x + y
  whiskerLeft x _ _ h := add_le_add_left h.le x |>.hom
  whiskerRight h y := add_le_add_right h.le y |>.hom
  tensorHom h₁ h₂ := add_le_add h₁.le h₂.le |>.hom
  tensorUnit := 0
  associator x y z := eqToIso <| add_assoc x y z
  leftUnitor x := eqToIso <| zero_add x
  rightUnitor x := eqToIso <| add_zero x

namespace CategoryTheory
open Quiver
class Dagger (C) [Category C] extends HasInvolutiveReverse C where
  reverse_id (a: C) : reverse (𝟙 a) = 𝟙 a
  reverse_comp {a b c: C} (f : a ⟶ b) (g: b ⟶ c) : reverse (g ⊚ f) = reverse f ⊚ reverse g
namespace Dagger
variable (C) [Category C] [Dagger C]

instance : Dagger (Cᵒᵖ) where
  reverse' f := ⟨reverse f.unop⟩
  inv' | f => Hom.unop_inj <| reverse_reverse f.unop
  reverse_id a := Hom.unop_inj <| reverse_id a.unop
  reverse_comp f g := Hom.unop_inj <| reverse_comp g.unop f.unop

def Functor.reverse : Cᵒᵖ ⥤ C where
  obj x := x.unop
  map f := Quiver.reverse f.unop
  map_id x := reverse_id x.unop
  map_comp f g := reverse_comp g.unop f.unop

theorem Functor.reverse_obj (x) : (reverse C).obj x = x.unop := rfl
theorem Functor.reverse_involutive : (reverse C).rightOp ⋙ (reverse C) = 𝟭 C := Functor.ext
  (fun _ ↦ rfl)
  fun _ _ f ↦ .symm <| Category.id_comp _ |>.trans <| Category.comp_id _ |>.trans <|
    reverse_reverse f |>.symm
end Dagger

def ECat (V) [Category V] [MonoidalCategory V] : Type _ := Bundled (EnrichedCategory V)
namespace ECat
variable (V) [Category V] [MonoidalCategory V]

instance : CoeSort (ECat V) (Type _) := ⟨Bundled.α⟩
instance : (C: ECat V) → EnrichedCategory V C := Bundled.str
def of (C) [EnrichedCategory V C] : ECat V := Bundled.of C

open EnrichedFunctor in
instance : Category (ECat V) where
  Hom C D := EnrichedFunctor V C D
  id C := id V C
  comp := comp V
  id_comp _ := .symm <| ext V (fun _ ↦ rfl) fun _ _ ↦
    Category.comp_id _ |>.trans <| Category.id_comp _ |>.symm
  comp_id _ := .symm <| ext V (fun _ ↦ rfl) fun _ _ ↦ rfl
  assoc _ _ _ := ext V (fun _ ↦ rfl) fun _ _ ↦ Category.comp_id _ |>.trans <| Category.assoc ..

end ECat

end CategoryTheory

open ENNReal
local notation "Cost" => ℝ≥0∞ᵒᵖ

abbrev LawvSpace := EnrichedCategory Cost
namespace LawvSpace

instance [LawvSpace X] : EDist X where
  edist x y := (x ⟶[Cost] y).unop

noncomputable instance [PseudoEMetricSpace X] : LawvSpace X where
  Hom x y := ⟨edist x y⟩
  id x := edist_self x |>.le.hom.op
  comp x y z := ⟨edist_triangle x y z |>.hom⟩

variable {X} [LawvSpace X] {x y : X}

open ForgetEnrichment in
theorem forgetIsThin : Quiver.IsThin (ForgetEnrichment Cost X) := fun _ _ ↦ {
  allEq f g := Subsingleton.elim (homTo Cost f) (homTo Cost g)
}

instance [LawvSpace X] [@IsSymmOp X Cost EnrichedCategory.Hom] : PseudoEMetricSpace X where
  edist a b := (a ⟶[Cost] b).unop
  edist_self x := le_bot_iff.mp (eId Cost x).unop.le
  edist_comm x y := congrArg _ (IsSymmOp.symm_op x y)
  edist_triangle x y z := eComp Cost x y z |>.unop.le

open Bundled

abbrev LMet := ECat Cost
namespace LMet

noncomputable
def homEquivShort (X Y : LMet) : (X ⟶ Y) ≃ {f: X → Y // ∀a b, edist (f a) (f b) ≤ edist a b} where
  toFun F := .mk F.obj (F.map · · |>.unop.le)
  invFun f := ⟨f, (f.prop · · |>.hom.op), fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LMet
end LawvSpace
