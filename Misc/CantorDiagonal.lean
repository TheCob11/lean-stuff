import Mathlib

open Function Cardinal
-- `cantor_surjective`
example (f: α → Set α) : ¬f.Surjective := fun h ↦
  let ⟨a, ha⟩ := h {a | a ∉ f a}
  iff_not_self <| Set.ext_iff.mp ha a

-- `cantor_injective`
example (f: Set α → α) : ¬f.Injective := fun h ↦
  cantor_surjective _ h.preimage_surjective

-- almost `cantor`
theorem Cardinal.lt_set : #α < #(Set α) :=
  mk_embedding_eq_zero_iff_lt.symm.trans Cardinal.mk_eq_zero_iff |>.mpr
    ⟨fun ⟨f, hf⟩ ↦ cantor_injective f hf⟩

-- `mk_set`
example : #(Set α) = 2 ^ #α := mk_congr <| Equiv.arrowCongr (.refl α) <|
  Fintype.equivFin Prop |>.trans Equiv.ulift.symm

-- `cantor`
example : #α < 2 ^ #α := mk_set.subst lt_set

-- noncomputable def binDigit (n: ℕ) : ℝ := (1/2) ^ n
-- open Classical in
-- noncomputable example : Set ℕ ↪ ℝ :=
--   let summand s n := if n ∈ s then binDigit n else 0
--   have summable s : Summable (summand s) :=
--     have (n) : summand s n = 0 ∨ summand s n = binDigit n := ite_eq_or_eq .. |>.symm
--     summable_geometric_two.summable_of_eq_zero_or_self this
--   let f := tsum ∘ summand
--   have hf s t h := by
--     have ⟨x, hx⟩ : Summable (summand s) := summable s
--     have ⟨y, hy⟩ : Summable (summand t) := summable t
--     have : x = y := HasSum.tsum_eq hx |>.symm.trans h |>.trans <| HasSum.tsum_eq hy

--     sorry
--   ⟨f, hf⟩
--   -- sorry

example : (ℕ → ℕ) ↪ ℝ where
  toFun f :=
    let x: ContFract ℝ := sorry
    sorry
  inj' f g h := sorry
