import Mathlib
open CategoryTheory Limits MonoidalCategory
local notation f " ⊚ " g => CategoryStruct.comp g f

variable {C} [Category C] {c x y : C}

class IsUniversal (c: C) (F: Cᵒᵖ ⥤ Type) where
  pt: F.obj ⟨c⟩
  [prop: IsIso <| yonedaEquiv.symm pt]

namespace IsUniversal
instance [h: IsUniversal c F] : IsIso (yonedaEquiv.symm h.pt) := h.prop

noncomputable def repr [h: IsUniversal c F] : F.RepresentableBy c :=
  Functor.representableByEquiv.symm <| asIso <| yonedaEquiv.symm h.pt

noncomputable example : Nonempty (IsUniversal c F) ↔ Nonempty (F.RepresentableBy c) where
  mp | ⟨h⟩ => .intro h.repr
  mpr | ⟨h⟩ => .intro {
    pt := h.homEquiv (𝟙 c)
    prop := ⟨{
      app _ p := h.homEquiv.symm p
      naturality _ _ f := funext fun p ↦ h.comp_homEquiv_symm p f.unop |>.symm
    },
      NatTrans.ext <| funext₂ fun _ f ↦ h.homEquiv.symm_apply_eq.mpr <| h.homEquiv_eq f |>.symm,
      NatTrans.ext <| funext₂ fun _ f ↦ h.homEquiv_eq _ |>.symm.trans <| h.homEquiv.right_inv f⟩
  }

noncomputable
example [HasBinaryProduct x y] : IsUniversal (x ⨯ y) (yoneda.obj x ⊗ yoneda.obj y) where
  pt := (prod.fst, prod.snd)
  prop := .mk ⟨{
      app | _, (f, g) => prod.lift f g
      naturality _ _ _ := funext fun (_, _) ↦ prod.comp_lift .. |>.symm
    },
    NatTrans.ext <| funext₂ fun _ f ↦ calc prod.lift (prod.fst ⊚ f) (prod.snd ⊚ f)
      _ = prod.lift (prod.fst) (prod.snd) ⊚ f := prod.comp_lift .. |>.symm
      _ = 𝟙 _ ⊚ f := congrArg _ prod.lift_fst_snd
      _ = f := Category.comp_id f
    , NatTrans.ext <| funext₂ fun _ (f, g) ↦ Prod.ext (prod.lift_fst f g) (prod.lift_snd f g)⟩

example [Category J] (F: J ⥤ C) : HasLimit F ↔ ∃c, Nonempty (IsUniversal c F.cones) where
  mp | ⟨s, hs⟩ => .intro s.pt <| .intro {
    pt := s.π
    prop := .mk <| ⟨{
      app x π := hs.lift ⟨x.unop, π⟩
      naturality x y f := funext fun π ↦ by
        dsimp
        refine hs.hom_ext ?_
        sorry
    }, sorry, sorry⟩
  }
  mpr := sorry

noncomputable
example [Category J] (F: J ⥤ C) (s: Cone F) : IsLimit s ≃ IsUniversal s.pt F.cones where
  toFun hs := {
    pt := s.π
    prop := .mk ⟨{
      app x π := hs.lift ⟨x.unop, π⟩
      naturality x y f := funext fun π ↦ hs.hom_ext fun j ↦ calc
        _ = π.app j ⊚ f.unop := hs.fac ⟨y.unop, π ⊚ _⟩ j
        _ = (s.π.app j ⊚ hs.lift ⟨x.unop, π⟩) ⊚ f.unop := congrArg _ <| hs.fac ⟨x.unop, π⟩ j |>.symm
        _ = _ := Category.assoc .. |>.symm
    }, NatTrans.ext <| funext₂ fun _ f ↦ hs.hom_lift _ |>.symm,
       NatTrans.ext <| funext₂ fun _ f ↦ NatTrans.ext <| funext fun j ↦ hs.fac ⟨_, f⟩ j⟩
  }
  invFun h := {
    lift t := inv (yonedaEquiv.symm h.pt) |>.app ⟨t.pt⟩ t.π
    fac t j := by
      simp [yonedaEquiv]
      have := yonedaEquiv.symm h.pt |>.app ⟨s.pt⟩

      sorry
    uniq := sorry
  }
  -- invFun h := Limits.equiv sorry
  left_inv := sorry
  right_inv := sorry
