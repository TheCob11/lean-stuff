import Mathlib

section KnasterTarski
variable {L} [CompleteLattice L] (f: L →o L)

-- `OrderHom.gfp`
example : Function.IsFixedPt f (sSup {x | x ≤ f x}) :=
  have hle : sSup _ ≤ f (sSup _) := sSup_le fun _s hs ↦ hs.trans <| f.mono (le_sSup hs)
  hle.antisymm' <| le_sSup (f.mono hle)

example : CompleteLattice ({x // f x = x}) := @completeLatticeOfSup _ _
  ⟨fun S ↦ ⟨sInf {x ∈ Set.Ici (sSup (Subtype.val '' S)) | f x ≤ x},
    let sUp := {x ∈ Set.Ici (sSup (Subtype.val '' S)) | f x ≤ x}
    have hle : sSup (Subtype.val '' S) ≤ f (sInf sUp) := sSup_le fun _x ⟨⟨s, hs⟩, hsS, hsx⟩ ↦
      hsx.symm.trans_le <| hs.symm.trans_le <|
        f.mono <| le_sInf fun _b hb ↦ sSup_le_iff.mp hb.1 s ⟨⟨s, hs⟩, hsS, rfl⟩
    have : f (sInf sUp) ≤ sInf sUp := le_sInf fun _b hb ↦ (f.mono (sInf_le hb)).trans hb.2
    this.antisymm <| sInf_le ⟨hle, f.mono this⟩⟩⟩
  fun S ↦ {
    left | ⟨s, hs⟩, hsS => le_sInf fun _b ⟨hbS, _⟩ ↦ le_sSup (s:=_ '' S) ⟨⟨s, hs⟩, hsS, rfl⟩ |>.trans hbS
    right | ⟨_s, hs⟩, hsup => sInf_le ⟨sSup_le fun _ ⟨__x, hxS, hxt⟩ ↦ hxt ▸ hsup hxS, hs.le⟩
  }

end KnasterTarski
lemma Set.image_monotone : Monotone (Set.image f) := fun _ _ ↦ Set.image_mono

noncomputable example [Nonempty α] [Nonempty β] (f: α ↪ β) (g: β ↪ α) : α ≃ β :=
  let φ : Set α →o Set α := {
    toFun A := (g '' (f '' A)ᶜ)ᶜ
    monotone' := compl_anti.comp <| Set.image_monotone.comp_antitone <|
      compl_anti.comp_monotone Set.image_monotone
  }
  let A := φ.gfp
  have Ac_eq : Aᶜ = g '' (f '' A)ᶜ := compl_eq_comm.mp φ.map_gfp
  have hA : Aᶜ ⊆ Set.range g := Ac_eq.substr <| Set.image_subset_range g _
  let f' := Function.invFun f
  have hf' : f'.LeftInverse f := Function.leftInverse_invFun f.injective
  let g' := Function.invFun g
  have hg' : g'.LeftInverse g := Function.leftInverse_invFun g.injective
  haveI := Classical.dec
{
  toFun := A.piecewise f g'
  invFun := (f '' A).piecewise f' g
  left_inv a := by
    dsimp [Set.piecewise, Set.image]
    split
    next ha =>
      simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq_right, ha, ↓reduceIte];
      exact hf' a
    next ha =>
      have : ¬∃a₁ ∈ A, f a₁ = g' a := fun ⟨a₁, ha₁, ha₁a⟩ ↦
        let ⟨b, hb, hba⟩ := Ac_eq.subset ha
        have : f a₁ = b := g.injective <| calc
          _ = g (g' a) := congrArg g ha₁a
          _ = a := Function.invFun_eq ⟨b, hba⟩
          _ = g b := hba.symm
        hb ⟨a₁, ha₁, this⟩
      exact (if_neg this).trans <| Function.invFun_eq (hA ha)
  right_inv b := by
    dsimp [Set.piecewise, Set.image]
    split
    next hb =>
      let ⟨a, haA, hab⟩ := hb
      have : f' b ∈ A := by_contra fun h ↦ absurd haA <| hf' a ▸ hab.substr h
      exact (if_pos this).trans <| Function.invFun_eq ⟨a, hab⟩
    next hb =>
      have : g b ∉ A := Ac_eq.superset ⟨b, hb, rfl⟩
      exact (if_neg this).trans <| hg' b }

-- namespace Goldmakher
-- variable {α β : Type u} (f: α ↪ β) (g: β ↪ α)

-- mutual
-- def A : ℕ → Set α
-- | 0 => Set.univ
-- | n + 1 => g '' (B n)

-- def B : ℕ → Set β
-- | 0 => Set.univ
-- | n + 1 => f '' (A n)
-- end

-- def A_equiv_2n : ∀n, (A f g n) ≃ A f g (2 * n) := Nat.rec
--   (mul_zero 2 ▸ Equiv.refl _)
--   (fun n ih ↦ sorry)

-- lemma A_anti : Antitone (A f g) := Nat.recAux
--   (fun _ _ ↦ le_top)
--   (fun n ih m hm ↦ sorry)

-- end Goldmakher
