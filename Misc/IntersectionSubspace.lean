import Mathlib

example {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M]
  (S₁ S₂ : Submodule R M) : Submodule R M where
  carrier := S₁ ∩ S₂
  add_mem' ha hb :=
    Set.mem_inter (S₁.add_mem' ha.left hb.left) (S₂.add_mem' ha.right hb.right)
  zero_mem' :=
    Set.mem_inter S₁.zero_mem' S₂.zero_mem'
  smul_mem' r _ hm :=
    Set.mem_inter (S₁.smul_mem' r hm.left) (S₂.smul_mem' r hm.right)

example {R M : Type*} [AddCommGroup M] [Ring R] [Module R M]
  (S₁ S₂ S : Submodule R M) (hS: S.carrier = S₁.carrier ∪ S₂.carrier) :
  S₁.carrier ⊆ S₂.carrier ∨ S₂.carrier ⊆ S₁.carrier := by_contra fun h ↦
    have ⟨⟨s₁, ⟨s₁_mem₁, hs₁⟩⟩, ⟨s₂, ⟨s₂_mem₂, hs₂⟩⟩⟩ := not_or.mp h |>.imp
      Set.not_subset_iff_exists_mem_not_mem.mp
      Set.not_subset_iff_exists_mem_not_mem.mp
    have s₁_mem : s₁ ∈ S.carrier := hS ▸ Set.mem_union_left S₂ s₁_mem₁
    have s₂_mem : s₂ ∈ S.carrier := hS ▸ Set.mem_union_right S₁ s₂_mem₂
    match Set.mem_or_mem_of_mem_union <| hS ▸ S.add_mem' s₁_mem s₂_mem with
    | .inl s_mem₁ => hs₂ <| (S₁.add_mem_iff_right s₁_mem₁).mp s_mem₁
    | .inr s_mem₂ => hs₁ <| (S₂.add_mem_iff_left s₂_mem₂).mp s_mem₂
