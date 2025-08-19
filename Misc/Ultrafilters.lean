import Mathlib
open Filter
variable {α}
infixr:25 " →ᵇ " => BoundedLatticeHom

example (f: Filter α) [f.NeBot] (s: Set α) (hs: s ∈ f) : sᶜ ∉ f :=
  fun h ↦ f.empty_not_mem <| s.inter_compl_self ▸ f.inter_mem hs h

example (f: Ultrafilter α) (s: Set α) (hs: sᶜ ∉ f) : s ∈ f := sorry

-- example (f: Ultrafilter α) (s: Set α) : s ∈ f ↔ sᶜ ∉ f

example : Ultrafilter α ≃ {f : Filter α // ∀s : Set α, s ∈ f ∨ sᶜ ∈ f} where
  toFun f := ⟨f, sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

example : Ultrafilter α ≃ (Set α →ᵇ Prop) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
