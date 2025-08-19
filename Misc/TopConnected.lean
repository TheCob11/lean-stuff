import Mathlib

variable {ι} (X) (Y: ι → Type*) [TopologicalSpace X] [∀i, TopologicalSpace (Y i)]

def sigmaCodMap [TopologicalSpace X] [∀i, TopologicalSpace (Y i)]
  : (Σi, C(X, Y i)) → C(X, Σi, Y i) := fun ⟨i, f⟩ ↦ .comp (.sigmaMk i) f

recall isOpen_range_sigmaMk {i} : IsOpen (Set.range (@Sigma.mk _ Y i)) :=
  Set.image_univ.subst <| isOpen_sigma_iff.mpr fun j ↦ by
  if hij: i = j then exact hij ▸ sigma_mk_preimage_image_eq_self ▸ isOpen_univ
  else exact sigma_mk_preimage_image' hij ▸ isOpen_empty

recall isClopen_range_sigmaMk {i} : IsClopen (Set.range (@Sigma.mk _ Y i)) where
  right := isOpen_range_sigmaMk
  left.isOpen_compl :=
    have : (Set.range (@Sigma.mk _ Y i))ᶜ = ⋃j ≠ i, Set.range (Sigma.mk j) := calc
      _ = (Sigma.fst ⁻¹' {i})ᶜ := congrArg _ <| Set.range_sigmaMk i
      _ = Sigma.fst ⁻¹' {i}ᶜ := rfl
      _ = Sigma.fst ⁻¹' {j | j ≠ i} := congrArg _ <| Set.compl_singleton_eq i
      _ = Sigma.fst ⁻¹' ⋃j ≠ i, {j} := congrArg _ <| .symm <| Set.biUnion_of_singleton _
      _ = ⋃j ≠ i, Sigma.fst ⁻¹' {j} := Set.preimage_iUnion₂
      _ = ⋃j ≠ i, Set.range (Sigma.mk j) := Set.iUnion₂_congr fun j _ ↦ (Set.range_sigmaMk j).symm
    this ▸ isOpen_biUnion fun _ _ ↦ isOpen_range_sigmaMk


example : ConnectedSpace X ↔
  (∀{ι} (Y: ι → _) [∀i, TopologicalSpace (Y i)], (sigmaCodMap X Y).Bijective) where
  mp hX {ι} Y _ := {
    left
    | ⟨i, f⟩, ⟨j, g⟩, hfg => by
      let ⟨ij_eq, fg_eq⟩ := forall_and_left (i = j) _ |>.mp
        fun x ↦ Sigma.ext_iff.mp <| DFunLike.congr_fun hfg x
      subst ij_eq
      refine Sigma.ext rfl <| Eq.heq <| ContinuousMap.ext ?_
      simpa only [heq_eq_eq] using fg_eq
    right f :=
      let ⟨x₀⟩ := inferInstanceAs (Nonempty X)
      let i := (f x₀).fst
      let Yis := Set.range (@Sigma.mk _ Y i)
      have : f ⁻¹' Yis = Set.univ :=
        have : IsClopen (f ⁻¹' Yis) := isClopen_range_sigmaMk.preimage f.continuous
        isClopen_iff.mp this |>.resolve_left <| Set.nonempty_iff_ne_empty.mp ⟨x₀, _, rfl⟩
      -- have (x) : (f x).fst = i :=
      --   (congrArg (f ⁻¹' ·) (Set.range_sigmaMk i)).symm.trans this |>.superset trivial
      let g' := this ▸ f.restrictPreimage (Set.range (Sigma.mk i))
      let unga : C(X, @Set.univ X) := {
        toFun x := ⟨x, trivial⟩
        continuous_toFun := .subtype_mk continuous_id' _
      }
      -- let bunga : C()
      by

      sorry

  }
  mpr hX := sorry
