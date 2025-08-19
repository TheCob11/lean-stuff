import Mathlib
open CategoryTheory

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
section Lim
variable {C I} [Category C] [Category I] (M: I ⥤ C)
-- starting with the def from stacks
structure Lim where
  pt: C
  π (i: I) : pt ⟶ M.obj i
  natl {i i' : I} (φ: i ⟶ i') : π i' = M.map φ ⊚ π i := by aesop_cat
  unique_fac {W: C} (q: (i: I) → (W ⟶ M.obj i)) (hq: ∀{i i'} (φ: i ⟶ i'), q i' = M.map φ ⊚ q i) :
    ∃!q': W ⟶ pt, ∀i, (π i ⊚ q') = q i := by aesop_cat
section LimProduct
example (X: Fin 2 → Type _) : Lim (Discrete.functor X) where
  pt := X 0 × X 1
  π
  | ⟨0⟩, ⟨x, _⟩ => x
  | ⟨1⟩, ⟨_, x⟩ => x
  natl := @fun ⟨i⟩ ⟨i'⟩ ⟨⟨(h: i = i')⟩⟩ ↦ h ▸ rfl
  unique_fac q _ :=
  ⟨ fun w ↦ ⟨q ⟨0⟩ w, q ⟨1⟩ w⟩,
    fun | ⟨0⟩ | ⟨1⟩ => rfl,
    fun _ _ ↦ by simp_all only [types_comp_apply, Eq.comm] ⟩

example (X: ι → Type) : Lim (Discrete.functor X) where
  pt := ∀i, X i
  π | ⟨i⟩, f => f i
  natl := @fun ⟨i⟩ ⟨i'⟩ ⟨⟨(h: i = i')⟩⟩ ↦ h ▸ rfl
  unique_fac q _ :=
  ⟨ fun w i ↦ q ⟨i⟩ w,
    fun _ ↦ rfl,
    fun _ _ ↦ by simp_all only [types_comp_apply, Eq.comm] ⟩
end LimProduct
section ConeProduct
def prodCone (X: ι → Type) : Limits.Cone (Discrete.functor X) where
  pt := ∀i, X i
  π := {
    app := fun ⟨i⟩ f ↦ f i
    naturality := fun ⟨i⟩ ⟨i'⟩ ⟨⟨(h: i = i')⟩⟩ ↦ by subst h; exact rfl
  }

example (X: ι → Type) : Limits.IsLimit (prodCone X) where
  lift c x i := c.π.app ⟨i⟩ x
  fac _ _ := rfl
  uniq _ φ hφ := funext₂ fun p i ↦ congrArg (φ p i = · p) (hφ ⟨i⟩).symm |>.mpr rfl
    -- by simp only [(hφ ⟨i⟩).symm]; exact rfl
end ConeProduct
section LimConeIso
example (s: Limits.Cone M) {i i' : I} (φ : i ⟶ i') : s.π.app i' = M.map φ ⊚ s.π.app i :=
  Category.id_comp (s.π.app _) |>.symm.trans <| s.π.naturality φ

example (s: Limits.Cone M) {i i' : I} (φ : i ⟶ i') : s.π.app i' = M.map φ ⊚ s.π.app i :=
  Category.id_comp (s.π.app _) |>.symm.trans <| s.π.naturality φ

variable {M}

def Lim.ofIsLimit {c: Limits.Cone M} (h: Limits.IsLimit c) : Lim M where
  pt := c.pt
  π := fun i ↦ c.π.app i
  natl := (Category.id_comp (c.π.app _) |>.symm.trans <| c.π.naturality ·)
  unique_fac := fun {W} q hq ↦
    let s := ⟨W, .mk q⟩
    .intro (h.lift s) (h.fac s) (h.uniq s)

def Lim.toCone (l: Lim M) : Limits.Cone M where
  pt := l.pt
  π := {
    app := l.π
    naturality := fun _ i' φ ↦ Category.id_comp (l.π i') |>.trans <| l.natl φ
  }

noncomputable
def Lim.toCone_isLimit (l: Lim M) : Limits.IsLimit l.toCone := .ofExistsUnique fun s ↦
  l.unique_fac s.π.app (fun φ ↦ s.w φ |>.symm)

noncomputable
def Lim.isoIsLimit : Lim M ≅ (c: Limits.Cone M) × Limits.IsLimit c where
  hom l := ⟨l.toCone, l.toCone_isLimit⟩
  inv | ⟨_, hc⟩ => .ofIsLimit hc
  hom_inv_id := rfl
  -- inv_hom_id := by aesop_cat -- uses uniqueness :/

end LimConeIso
end Lim
-- now that I'm convinced of the cone definition, time to start using it
open Limits

section InfProduct
variable {α} [CompleteLattice α] (X: ι → α)

def infCone : Cone (Discrete.functor X) where
  pt := ⨅i, X i
  π := .mk fun ⟨i⟩ ↦ ⟨⟨iInf_le X i⟩⟩

example : IsLimit (infCone X) where
  lift s := ⟨⟨le_iInf fun i ↦ s.π.app ⟨i⟩ |>.down.down⟩⟩
  fac _ _ := rfl
  uniq _ _ _ := rfl
end InfProduct

example [Category I] [Category C] {F: I ⥤ C} (s: Cone F) : Subsingleton (IsLimit s) where
  allEq h₁ h₂ := IsLimit.mk.injEq _ _ _ _ _ _ |>.mpr <|
    funext fun x ↦ h₂.uniq x (h₁.lift x) (h₁.fac x)

example [Category C] (x: C) : IsTerminal x ≃ ∀y, Unique (y ⟶ x) where
  toFun | ⟨lift, _, uniq⟩, y => {
    default := lift <| asEmptyCone y
    uniq := (uniq (asEmptyCone y) · (·.as.elim))
  }
  invFun h := {
    lift := fun ⟨y, _⟩ ↦ h y |>.default
    fac := fun _ ↦ (·.as.elim)
    uniq := fun s f _ ↦ h s.pt |>.uniq f
  }
  left_inv h := @Subsingleton.elim _ _ _ h
  right_inv _ := rfl

section MyProd
variable {C J} [Category C]

structure MyProd1 (F: J → C) where
  pt: C
  homEquiv {X}: (X ⟶ pt) ≃ (∀j, X ⟶ F j)
  homEquiv_comp {X Y: C} (f: X ⟶ Y) (g: Y ⟶ pt): ∀j, homEquiv (g ⊚ f) j = (homEquiv g j) ⊚ f

namespace MyProd1
def ex_RR : MyProd1 (Bool.rec ℝ ℝ) where
  pt := ℝ × ℝ
  homEquiv := {
    toFun f j a := j.recOn (f a).fst (f a).snd
    invFun f a := (f false a, f true a)
    left_inv _ := rfl
    right_inv _ := funext <| Bool.rec rfl rfl
  }
  homEquiv_comp _ _ _ := rfl

variable {F: J → C} (p: MyProd1 F)

example : (Discrete.functor F).cones |>.RepresentableBy p.pt where
  homEquiv {X} := {
    toFun f := {
      app j := p.homEquiv f j.as
      naturality | ⟨i⟩, ⟨j⟩, ⟨⟨(h: i = j)⟩⟩ => h ▸
        (Category.id_comp (p.homEquiv f i) |>.trans <| Category.comp_id _ |>.symm)
    }
    invFun f := p.homEquiv.symm fun j ↦ f.app ⟨j⟩
    left_inv := p.homEquiv.symm.apply_symm_apply
    right_inv _ := NatTrans.ext <| funext fun j ↦ congrFun (p.homEquiv.apply_symm_apply _) j.as
  }
  homEquiv_comp {X Y} f g := NatTrans.ext <| funext fun ⟨j⟩ ↦ p.homEquiv_comp f g j

theorem homEquiv_eq {f: X ⟶ p.pt} : p.homEquiv f j = p.homEquiv (𝟙 p.pt) j ⊚ f :=
  congrArg (p.homEquiv · j) (Category.comp_id f) |>.symm.trans <| p.homEquiv_comp f (𝟙 _) j

def fan : Fan F := .mk p.pt <| p.homEquiv (𝟙 p.pt)

def lim : IsLimit p.fan := mkFanLimit p.fan
  (fun s ↦ p.homEquiv |>.symm fun j ↦ s.π.app ⟨j⟩)
  (fun s j ↦ p.homEquiv_eq.symm.substr <| congrFun (p.homEquiv.apply_symm_apply s.proj) j)
  (fun s _ h ↦ p.homEquiv.injective <| funext fun j ↦
    p.homEquiv.apply_symm_apply s.proj |>.substr <| p.homEquiv_eq.trans (h j))

end MyProd1

structure MyProd2 (F: J → C) where
  pt: C
  homIso : (Functor.const (Discrete J)).op ⋙ yoneda.obj (Discrete.functor F) |>.RepresentableBy pt
namespace MyProd2

example : MyProd2 (Bool.rec ℝ ℝ) where
  pt := ℝ × ℝ
  homIso := {
    homEquiv := {
      toFun f := {
        app b x := by dsimp; exact b.as.recOn (f x).1 (f x).2
        naturality | ⟨i⟩, ⟨j⟩, ⟨⟨(f: i = j)⟩⟩ => funext fun x ↦ by subst f; exact rfl
      }
      invFun s x := (s.app ⟨false⟩ x, s.app ⟨true⟩ x)
      left_inv _ := rfl
      right_inv _ := NatTrans.ext <| funext fun b ↦ by rcases b with ⟨⟨⟩⟩ <;> exact rfl
    }
    homEquiv_comp _ _ := rfl
  }
end MyProd2
end MyProd

variable {C J} [Category C] [Category J] (F: J ⥤ C)

-- `Cone.equiv`
example : Cone F ≅ (c: Cᵒᵖ) × F.cones.obj c where
  hom s := ⟨⟨s.pt⟩, s.π⟩
  inv | ⟨⟨c⟩, π⟩ => ⟨c, π⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

example [Category J] (F: J ⥤ C) : HasLimit F ↔ F.cones.IsRepresentable where
  mp | ⟨s, hs⟩ => ⟨s.pt, ⟨@fun c ↦ {
    toFun f := {
      app j := s.π.app j ⊚ f
      naturality {i j} g := calc
        _ = s.π.app j ⊚ f := Category.id_comp _
        _ = (F.map g ⊚ s.π.app i) ⊚ f := congrArg _ <| s.w g |>.symm
        _ = _ := Category.assoc f _ _ |>.symm
    }
    invFun t := hs.lift ⟨c, t⟩
    left_inv f := .symm <| hs.uniq ⟨c, _⟩ f fun _ ↦ rfl
    right_inv t := .symm <| t.ext <| funext fun j ↦ .symm <| hs.fac ⟨c, t⟩ j
  }, fun _ _ ↦ NatTrans.ext <| funext fun _ ↦ Category.assoc ..⟩⟩
  mpr | ⟨c, ⟨t⟩⟩ => .mk {
    cone := ⟨c, t.homEquiv <| 𝟙 c⟩
    isLimit := {
      lift s := t.homEquiv.symm s.π
      fac s j := (NatTrans.congr_app ·.symm j) <|
        t.homEquiv.apply_symm_apply _ |>.symm.trans <| t.homEquiv_eq (t.homEquiv.symm s.π)
      uniq _ f h := t.homEquiv.eq_symm_apply.mpr <| NatTrans.ext <| funext fun j ↦
        t.homEquiv_eq f |>.substr <| h j
    }
  }

example : HasTerminal C ↔ ((Functor.const Cᵒᵖ).obj Unit).IsRepresentable where
  mp _ := .mk <| .intro (⊤_ C) <| .intro {
    homEquiv := {
      toFun _ := ()
      invFun | () => terminalIsTerminal.from ..
      left_inv _ := terminalIsTerminal.hom_ext ..
      right_inv _ := rfl
    }
    homEquiv_comp _ _ := rfl
  }
  mpr | ⟨_, ⟨hc⟩⟩ => IsTerminal.hasTerminal <| .ofUniqueHom (fun _ ↦ hc.homEquiv.symm ())
                                                           fun _ _ ↦ hc.homEquiv.injective rfl

namespace TopSubspaceEqualizer
open TopCat
variable (X: TopCat)

def X't := Bool
instance : TopologicalSpace X't := ⊤

def X': TopCat := of X't

abbrev f₁ : X ⟶ X' := ofHom <| .const _ true
variable {X} (A: Set X)

noncomputable
abbrev f₂ : X ⟶ X' := ofHom ⟨A.boolIndicator, continuous_top⟩

noncomputable
def forkA : Fork (f₁ X) (f₂ A) := .ofι (P := of A) (ofHom ⟨_, continuous_subtype_val⟩) <|
  ext fun x ↦ A.mem_iff_boolIndicator x |>.mp x.prop |>.symm

theorem fork_pt_mem {A} (S: Fork (f₁ X) (f₂ A)) (s: S.pt): S.ι.hom s ∈ A :=
  A.mem_iff_boolIndicator _ |>.mpr <| .symm <| TopCat.ext_iff.mp S.condition s

noncomputable
example : IsLimit (forkA A) where
  lift (S: Fork _ _) := ofHom ⟨A.codRestrict _ <| fork_pt_mem S, S.ι.hom.continuous.codRestrict _⟩
  fac
  | _, .zero => rfl
  | S, .one => Fork.app_one_eq_ι_comp_left S ▸ rfl
  uniq (S: Fork _ _) f h := ext fun _ ↦ Subtype.ext <|
    have : S.ι = (ofHom ⟨_, continuous_subtype_val⟩ ⊚ f) := h .zero |>.symm
    Set.val_codRestrict_apply .. |>.symm.subst <| this.substr rfl

end TopSubspaceEqualizer

namespace CoproductsType
variable {ι} (F: ι → Type _)

def sumCone : Cocone (Discrete.functor F) where
  pt := Σi, F i
  ι := Discrete.natTrans fun i ↦ .mk i.as

example : IsColimit (sumCone F) where
  desc s x := s.ι.app ⟨x.1⟩ x.2
  fac _ _ := funext fun _ ↦ rfl
  uniq _ _ h := funext fun x ↦ h ⟨x.1⟩ ▸ rfl

end CoproductsType
