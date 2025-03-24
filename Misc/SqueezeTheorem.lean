import Mathlib
open Topology Filter

variable {α β} [TopologicalSpace β] [Preorder β] [OrderTopology β]
         {f g h : α → β} {la: Filter α} {b: β}
set_option autoImplicit false

-- `tendsto_order`
example : Tendsto f la (𝓝 b) ↔ (∀b' < b, ∀ᶠa in la, b' < f a) ∧ ∀b' > b, ∀ᶠa in la, f a < b' where
  mp h := {
    left := fun b' hb' ↦ h <| lt_mem_nhds hb'
    right := fun b' hb' ↦ h <| gt_mem_nhds hb'
  }
  mpr | ⟨hl, hr⟩, s, hs => sorry

example : Tendsto f la (𝓝 b) ↔ (∀b' < b, ∀ᶠa in la, b' < f a) ∧ ∀b' > b, ∀ᶠa in la, f a < b' :=
  Iff.symm <| calc
  _ ↔ (∀b' < b, ∀ᶠa in la, f a ∈ Set.Ioi b') ∧ (∀b' > b, ∀ᶠa in la, f a ∈ Set.Iio b') := Iff.rfl
  _ ↔ (∀b' < b, f ⁻¹' .Ioi b' ∈ la) ∧ (∀b' > b, f ⁻¹' .Iio b' ∈ la) := Iff.rfl
  _ ↔ (∀b' < b, Set.Ioi b' ∈ la.map f) ∧ (∀b' > b, Set.Iio b' ∈ la.map f) := Iff.rfl
  _ ↔ (∀b' ∈ Set.Iio b, Set.Ioi b' ∈ la.map f) ∧ (∀b' ∈ Set.Ioi b, Set.Iio b' ∈ la.map f) := Iff.rfl
  _ ↔ _ := {
    mp := fun ⟨hl, hr⟩ s hs ↦ sorry
    mpr := fun h ↦ {
      left := fun b' hb' ↦ h <| lt_mem_nhds hb'
      right := fun b' hb' ↦ h <| gt_mem_nhds hb'
    }
  }


example (hf: Tendsto f la (𝓝 b)) (hg: Tendsto g la (𝓝 b)) (hfh: f ≤ᶠ[la] h) (hhg: h ≤ᶠ[la] g) :
        Tendsto h la (𝓝 b) := tendsto_order.mpr
{ left := fun b' hb' ↦
    tendsto_order.mp hf |>.left  b' hb' |>.and hfh |>.mono fun _ ⟨hlt, hle⟩ ↦ hlt.trans_le hle
  right := fun b' hb' ↦
    tendsto_order.mp hg |>.right b' hb' |>.and hhg |>.mono fun _ ⟨hlt, hle⟩ ↦ hle.trans_lt hlt}
