import Mathlib

/- if we have a type α that can contain other αs (this is just notation) and it can faithfully
   represent sets of αs, then we get a contradiction, specifically with `{a | a ∉ a}` -/
theorem russell (α) [Membership α α] (mk: Set α → α) (hmk: ∀{s a}, a ∈ s ↔ a ∈ mk s) : False :=
  let a := mk {a | a ∉ a}
  have not_mem : a ∉ a := fun h ↦ hmk.mpr h h
  have mem : a ∈ a := hmk.mp not_mem
  not_mem mem

/-- info: 'russell' does not depend on any axioms -/
#guard_msgs in
#print axioms russell

/- slightly more suggestive interpretation: if this inclusion preserves set membership, then
   it's injective (which we shouldn't have from Set α → α) -/
example [Membership α α] (f: Set α → α) (hf: ∀{s a}, a ∈ s ↔ a ∈ f s) : f.Injective := fun _ _ hs ↦
  Set.ext fun _ ↦ {
    mp := fun h ↦ hf.mpr <| hs.subst <| hf.mp h
    mpr := fun h ↦ hf.mpr <| hs.substr <| hf.mp h
  }

open CategoryTheory Limits
local notation g:80 " ⊚ " f:80 => CategoryStruct.comp f g

def isPointSurjective [Category C] [HasTerminal C] {A B : C} (φ: A ⟶ B) : Prop :=
  ∀q: ⊤_ C ⟶ B, ∃p: ⊤_ C ⟶ A, φ ⊚ p = q
#print internalizeHom
example [Category C] [HasFiniteProducts C] [CartesianClosed C] (A B : C)
  (φ: A ⟶ B ^^ A) (hf: isPointSurjective φ) (f: B ⟶ B) : ∃b: ⊤_ C ⟶ B, f ⊚ b = b :=
  -- let eval := exp.ev A |>.app B
  -- let q : ⊤_ C ⟶ B ^^ A := internalizeHom <| f ⊚ eval ⊚ prod.lift (𝟙 A) φ
  -- #check (exp.ev A |>.app B   : A ⨯ B ^^ A ⟶ B)
  -- #check (exp.coev A |>.app B : B ⟶ (A ⨯ B) ^^ A)
  -- let ⟨p, hp⟩ := hf q
  -- let b: ⊤_ C ⟶ B := f ⊚ eval ⊚ prod.lift (𝟙 A) φ ⊚ p
  -- ⟨
  --   b,
  --   calc
  --     _ = f ⊚ f ⊚ eval ⊚ prod.lift (𝟙 A) φ ⊚ p := rfl
  --     _ = _ := sorry
  -- ⟩

  let φb := CartesianClosed.uncurry φ
  let unga := f ⊚ φb ⊚ diag A
  let ⟨k, hk⟩ := hf <| internalizeHom unga
  have (a: ⊤_ C ⟶ A): φb ⊚ (prod.lift a k) = f ⊚ φb ⊚ (prod.lift a a) := by
    dsimp [internalizeHom, unga, φb] at hk ⊢
    simp [CartesianClosed.uncurry_eq]


    sorry
  let b: ⊤_ C ⟶ B := unga ⊚ k

  sorry
