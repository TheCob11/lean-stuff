import Mathlib

section RusselsParadox

variable {α} [Membership α α]

/- if we have a type α that can contain other αs (this is just notation) and it can faithfully
   represent sets of αs, then we get a contradiction, specifically with `{a | a ∉ a}` -/
theorem russell (mk: Set α → α) (hmk: ∀{s a}, a ∈ s ↔ a ∈ mk s) : False :=
  let a := mk {a | a ∉ a}
  have not_mem : a ∉ a := fun h ↦ hmk.mpr h h
  have mem : a ∈ a := hmk.mp not_mem
  not_mem mem

/-- info: 'russell' does not depend on any axioms -/
#guard_msgs in
#print axioms russell

/- slightly more suggestive interpretation: if this inclusion preserves set membership, then
   it's injective (which we shouldn't have from Set α → α) -/
example (f: Set α → α) (hf: ∀{s a}, a ∈ s ↔ a ∈ f s) : f.Injective := fun _ _ hs ↦
  Set.ext fun _ ↦ hs ▸ hf |>.trans hf.symm

end RusselsParadox

section LawveresFixedPoint

open CategoryTheory CartesianClosed MonoidalCategory ChosenFiniteProducts
local notation g:80 " ⊚ " f:80 => CategoryStruct.comp f g
variable {C} [Category C] [ChosenFiniteProducts C] [CartesianClosed C] {A B : C}

def PointSurjective (φ: A ⟶ B) : Prop :=
  ∀q: 𝟙_ C ⟶ B, ∃p: 𝟙_ C ⟶ A, φ ⊚ p = q

abbrev diag (A: C) : A ⟶ A ⊗ A := lift (𝟙 A) (𝟙 A)

example (φ: A ⟶ B ^^ A) (hf: PointSurjective φ) (f: B ⟶ B) : ∃b: 𝟙_ C ⟶ B, f ⊚ b = b :=
  let eval : A ⊗ (B ^^ A) ⟶ B := exp.ev A |>.app B
  let q := f ⊚ uncurry φ ⊚ diag A
  let qint : 𝟙_ C ⟶ B ^^ A := internalizeHom q
  let ⟨p, hp⟩ := hf qint
⟨ uncurry φ ⊚ diag A ⊚ p, .symm <| calc
    _ = uncurry φ ⊚ lift p p := by simp only [comp_lift, Category.comp_id]
    _ = (eval ⊚ A ◁ φ) ⊚ lift p p := rfl
    _ = eval ⊚ lift p (φ ⊚ p) := lift_whiskerLeft_assoc p p φ eval
    _ = eval ⊚ lift p (qint ⊚ 𝟙 _) := by rw [hp, Category.id_comp]
    _ = (eval ⊚ A ◁ qint) ⊚ lift p (𝟙 _) := lift_whiskerLeft_assoc p (𝟙 _) qint eval |>.symm
    _ = uncurry qint ⊚ lift p (𝟙 _) := rfl
    _ = uncurry (curry (q ⊚ fst _ _)) ⊚ lift p (𝟙 _) := rfl
    _ = (q ⊚ fst _ _) ⊚ lift p (𝟙 _) := by rw [uncurry_curry]
    _ = f ⊚ uncurry φ ⊚ diag A ⊚ p := by simp only [q, ← Category.assoc, lift_fst] ⟩

def WeaklyPointSurjective (φ: X ⟶ B ^^ A) : Prop :=
  ∀f: A ⟶ B, ∃x: 𝟙_ C ⟶ X, ∀a: 𝟙_ C ⟶ A, uncurry φ ⊚ lift a x = f ⊚ a

theorem PointSurjective.weak {φ: X ⟶ B ^^ A} (hφ: PointSurjective φ) : WeaklyPointSurjective φ :=
  fun f ↦
  let eval := exp.ev A |>.app B
  let fint := internalizeHom f
  hφ fint |>.imp fun x h a ↦ calc
    _ = (eval ⊚ A ◁ φ) ⊚ lift a x := rfl
    _ = eval ⊚ lift a (φ ⊚ x) := lift_whiskerLeft_assoc a x φ eval
    _ = eval ⊚ lift a (fint ⊚ 𝟙 _) := by rw [h, Category.id_comp]
    _ = (eval ⊚ A ◁ fint) ⊚ lift a (𝟙 _) := lift_whiskerLeft_assoc a (𝟙 _) fint eval |>.symm
    _ = uncurry fint ⊚ lift a (𝟙 _) := rfl
    _ = f ⊚ a := by simp only [internalizeHom, uncurry_curry, lift_fst_assoc, fint]

theorem lawvere {φ: A ⟶ B ^^ A} (hφ: WeaklyPointSurjective φ) (f: B ⟶ B) : ∃b: 𝟙_ C ⟶ B, f ⊚ b = b :=
  let eval : A ⊗ (B ^^ A) ⟶ B := exp.ev A |>.app B
  let qext := f ⊚ uncurry φ ⊚ diag A
  let q : 𝟙_ C ⟶ B ^^ A := internalizeHom qext
  let ⟨p, hp⟩ := hφ qext
⟨ uncurry φ ⊚ diag A ⊚ p, .symm <| calc
    _ = uncurry φ ⊚ lift p p := by simp only [comp_lift, Category.comp_id]
    _ = qext ⊚ p := hp p
    _ = f ⊚ uncurry φ ⊚ diag A ⊚ p := by simp only [qext, ← Category.assoc, lift_fst] ⟩


end LawveresFixedPoint
