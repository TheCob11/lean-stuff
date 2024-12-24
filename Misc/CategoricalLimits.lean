import Mathlib
open CategoryTheory

local notation f " ⊚ " g => CategoryStruct.comp g f
variable {C I} [Category C] [Category I] (M: I ⥤ C)
-- starting with the def from stacks
structure Lim where
  pt: C
  π (i: I) : pt ⟶ M.obj i
  natl {i i' : I} (φ: i ⟶ i') : π i' = M.map φ ⊚ π i := by aesop_cat
  unique_fac {W: C} (q: (i: I) → (W ⟶ M.obj i)) (hq: ∀{i i'} (φ: i ⟶ i'), q i' = M.map φ ⊚ q i) :
    ∃!q': W ⟶ pt, ∀i, (π i ⊚ q') = q i := by aesop_cat

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
