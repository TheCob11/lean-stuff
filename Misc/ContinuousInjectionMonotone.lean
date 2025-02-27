import Mathlib
open Topology

-- `Monotone.strictMono_of_injective`
example [LinearOrder α] [PartialOrder β] {f: α → β} (f_mono: Monotone f) (f_inj: f.Injective) :
  StrictMono f := fun _ _ h ↦ f_mono h.le |>.lt_of_ne <| f_inj.ne h.ne

variable {α β}
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
  {f: α → β}

example (hf: Continuous f) (f_inj: f.Injective) : StrictMono f ∨ StrictAnti f :=
  Or.imp (·.strictMono_of_injective f_inj) (·.strictAnti_of_injective f_inj) <| by_contra fun hnor ↦
  let ⟨a, b, c, a_lt, b_lt, habc⟩ := not_monotone_not_antitone_iff_exists_lt_lt.mp <| not_or.mp hnor
  match habc with
  | .inl ⟨fa_lt, fc_lt⟩ =>
    have : f a ⊔ f c < f b := sup_lt_iff.mpr ⟨fa_lt, fc_lt⟩
    let ⟨ab, ⟨_, ab_lt⟩, hfab⟩ := intermediate_value_Ico  a_lt.le hf.continuousOn ⟨le_sup_left , this⟩
    let ⟨bc, ⟨bc_gt, _⟩, hfbc⟩ := intermediate_value_Ioc' b_lt.le hf.continuousOn ⟨le_sup_right, this⟩
    have : ab ≠ bc := ab_lt.trans bc_gt |>.ne
    this <| f_inj <| hfab.trans hfbc.symm
  | .inr ⟨fa_gt, fc_gt⟩ =>
    have : f b < f a ⊓ f c := lt_inf_iff.mpr ⟨fa_gt, fc_gt⟩
    let ⟨ab, ⟨_, ab_lt⟩, hfab⟩ := intermediate_value_Ico' a_lt.le hf.continuousOn ⟨this, inf_le_left⟩
    let ⟨bc, ⟨bc_gt, _⟩, hfbc⟩ := intermediate_value_Ioc  b_lt.le hf.continuousOn ⟨this, inf_le_right⟩
    have : ab ≠ bc := ab_lt.trans bc_gt |>.ne
    this <| f_inj <| hfab.trans hfbc.symm
