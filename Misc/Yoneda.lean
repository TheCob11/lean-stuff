import Mathlib
open CategoryTheory Category

namespace MyYoneda

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g -- sorry
universe v u
variable (C: Type u) [Category.{v, u} C]

abbrev PSh := Cᵒᵖ ⥤ Type v
variable {C}
def yoneda : C ⥤ PSh C where
  obj c := {
    obj x := x.unop ⟶ c
    map f := (· ⊚ f.unop)
    map_id _ := funext id_comp
    map_comp _ _ := funext unop_comp_assoc
  }
  map f := {
    app _ := (f ⊚ ·)
    naturality _ _ g := funext (assoc g.unop · f)
  }
  map_id _ := NatTrans.ext <| funext₂ fun _ ↦ comp_id
  map_comp f g := NatTrans.ext <| funext₂ fun _ ↦ (assoc · f g |>.symm)

def yonedaFullyFaithful : @yoneda C _ |>.FullyFaithful where
  preimage {x _} s := s.app ⟨x⟩ (𝟙 x)
  map_preimage {x _} s := NatTrans.ext <| funext₂ fun ⟨z⟩ f ↦ calc
      s.app ⟨x⟩ (𝟙 x) ⊚ f = s.app ⟨z⟩ (𝟙 x ⊚ f) := congrFun (s.naturality f.op).symm (𝟙 x)
      _ = s.app ⟨z⟩ f := congrArg _ <| comp_id f
  preimage_map := id_comp

instance : @yoneda C _ |>.Full := yonedaFullyFaithful.full
instance : @yoneda C _ |>.Faithful := yonedaFullyFaithful.faithful

def yonedaEval : Cᵒᵖ ⥤ PSh C ⥤ Type _ where
  obj x := {
    obj F := F.obj x
    map α := α.app x
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  map f := {
    app F := F.map f
    naturality _ _ α := α.naturality f |>.symm
  }
  map_id x := NatTrans.ext <| funext (·.map_id x)
  map_comp f g := NatTrans.ext <| funext (·.map_comp f g)

def yonedaPairing : Cᵒᵖ ⥤ PSh C ⥤ Type _ where
  obj x := {
    obj F := yoneda.obj x.unop ⟶ F
    map α β := α ⊚ β
    map_id _ := rfl
    map_comp _ _ := rfl
  }
  map f := {
    app _ α := α ⊚ yoneda.map f.unop
    naturality _ _ _ := funext fun _ ↦ rfl
  }
  map_id x := NatTrans.ext <| funext₂ fun _ α ↦ yoneda.map_id x.unop ▸ id_comp α
  map_comp _ _ := NatTrans.ext<|funext₂ fun _ α ↦congr(α ⊚ $(Functor.map_comp ..)).trans (assoc ..)

def yonedaEvalUncurried : (Cᵒᵖ × PSh C) ⥤ Type _ where
  obj p := p.2.obj p.1
  map {p1 p2} f := p2.2.map f.1 ⊚ f.2.app p1.1
  map_id | ⟨x, F⟩ => F.map_id x ▸ id_comp (F.map (𝟙 x))
  map_comp := @fun (x, F) (y, G) (z, H) (f, α) (g, β) ↦ calc H.map (g ⊚ f) ⊚ β.app x ⊚ α.app x
    _ = (H.map g ⊚ H.map f) ⊚ β.app x ⊚ α.app x := congrArg _ (H.map_comp f g)
    _ = H.map g ⊚ (H.map f ⊚ β.app x) ⊚ α.app x := by simp only [assoc]
    _ = H.map g ⊚ (β.app y ⊚ G.map f) ⊚ α.app x := congrArg (_ ⊚ · ⊚ _) (β.naturality f |>.symm)
    _ = (H.map g ⊚ β.app y) ⊚ G.map f ⊚ α.app x := by simp only [assoc]

def yonedaPairingUncurried : (Cᵒᵖ × PSh C) ⥤ Type _ where
  obj p := yoneda.obj p.1.unop ⟶ p.2
  map := @fun (x, F) (y, G) (f, α) β ↦ {
    app z := α ⊚ β ⊚ yoneda.map f.unop |>.app z
    naturality z w g := funext fun h ↦
      by
      dsimp at β f α
      dsimp [yoneda] at h ⊢
      -- #check congrFun (α.naturality g) (β.app z (f.unop ⊚ h))
      -- simp [← α.naturality g]
      refine Eq.trans ?_ <| congrFun (α.naturality g) (β.app z (f.unop ⊚ h))
      -- #check congrFun (β.naturality g) (f.unop ⊚ h)
      sorry
  }
  map_id := sorry
  map_comp := sorry

def yonedaLemma : @yonedaPairing C _ ≅ yonedaEval ⋙ (whiskeringRight ..|>.obj uliftFunctor) :=
  NatIso.ofComponents
    (fun x ↦ NatIso.ofComponents (fun F ↦
    { hom α := .up <| α.app x (𝟙 x.unop)
      inv a :=
      { app _ f := F.map f.op a.down
        naturality _ _ f := funext fun g ↦ congrFun (F.map_comp g.op f) a.down }
      hom_inv_id := funext fun α ↦ NatTrans.ext <| funext₂ fun _ f ↦
        congrFun (α.naturality f.op) (𝟙 x.unop) |>.symm.trans <| congrArg _ (comp_id f)
      inv_hom_id := funext fun a ↦ ULift.ext _ a <| congrFun (F.map_id x) a.down })
      fun _ ↦ funext fun _ ↦ rfl)
    fun f ↦ NatTrans.ext <| funext₂ fun _ α  ↦ ULift.ext _ _ <| congrArg (α.app _)
      ((id_comp f.unop).trans (comp_id f.unop).symm) |>.trans <| congrFun (α.naturality f) (𝟙 _)

def yonedaLemma₂ : uncurry.obj (@yonedaPairing C _) ≅ uncurry.obj yonedaEval ⋙ uliftFunctor :=
  NatIso.ofComponents (fun ⟨x, F⟩ ↦
  { hom α := .up <| α.app x (𝟙 x.unop)
    inv a :=
    { app _ f := F.map f.op a.down
      naturality _ _ f := funext fun g ↦ congrFun (F.map_comp g.op f) a.down }
    hom_inv_id := funext fun α ↦ NatTrans.ext <| funext₂ fun _ f ↦
      congrFun (α.naturality f.op) (𝟙 x.unop) |>.symm.trans <| congrArg _ (comp_id f)
    inv_hom_id := funext fun a ↦ ULift.ext _ a <| congrFun (F.map_id x) a.down })
  fun ⟨f, α⟩ ↦ funext fun β ↦ ULift.ext _ _ <| congrArg (α.app _) <| congrArg (β.app _)
    ((id_comp f.unop).trans (comp_id f.unop).symm) |>.trans <| congrFun (β.naturality f) (𝟙 _)
