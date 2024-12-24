import Mathlib

-- funext, propext, and choice imply excluded middle
theorem diaconescu
  -- the Nontrivial type to work with, mathlib just uses Prop
  (α: Type _) [Nontrivial α]
  -- axioms, restricted to α and Prop bc that's all we need here
  -- we also only need a weaker (i think) version of funext+propext
  (funext_of_and : ∀{f g : α → Prop}, (∀x, f x ∧ g x) → f = g)
  (choose : ∀{p: α → Prop}, Exists p → α) (choose_spec : ∀{p} (h: Exists p), p (choose h))
  -- important part
  (p: Prop) : p ∨ ¬p :=

  let ⟨a, b, hab⟩ := @Nontrivial.exists_pair_ne α _
  let U (x: α) : Prop := p ∨ x = a
  let V (x: α) : Prop := p ∨ x = b
  /- note: can't just unpack these into x and hx (choiceless!)
     because we'll need them to be related to hX later -/
  have hU : Exists U := ⟨a, .inr rfl⟩
  have hV : Exists V := ⟨b, .inr rfl⟩
  let u := choose hU
  let v := choose hV
  have p_or_ne : p ∨ u ≠ v :=
    have : (p ∨ u = a) ∧ (p ∨ v = b) := ⟨choose_spec hU, choose_spec hV⟩
    have : p ∨ u = a ∧ v = b := or_and_left.mpr this
    this.imp_right fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ hab
  have p_imp_eq (hp: p) : u = v :=
    -- this is where we (really) use those axioms
    have : U = V := funext_of_and fun _ ↦ ⟨.inl hp, .inl hp⟩
    have : ∀(h₀: Exists U) (h₁: Exists V), choose h₀ = choose h₁ :=
      -- (congrArg (∀(h₀ : Exists ·) (h₁ : Exists V), choose h₀ = choose h₁) this).mpr fun _ _ ↦ rfl
      -- begrudgingly using tactics here because its probably way cleaner
      by rw [this]; exact fun _ _ ↦ rfl
    this hU hV
  p_or_ne.imp_right p_imp_eq.mt

/-- info: 'diaconescu' does not depend on any axioms -/
#guard_msgs in
#print axioms diaconescu

-- mathlib version (essentially)
example : (p: Prop) → p ∨ ¬p := diaconescu Prop
  (fun h ↦ funext fun x ↦ propext ⟨fun _ ↦ (h x).right, fun _ ↦ (h x).left⟩)
  Exists.choose Exists.choose_spec
