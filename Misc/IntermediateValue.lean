import Mathlib

variable {X} [TopologicalSpace X]

example : PreconnectedSpace X ↔ ∀{s: Set X}, IsClopen s ↔ s = ∅ ∨ s = .univ where
  mp _ s := {
    mp := fun ⟨⟨sc_open⟩, s_open⟩ ↦ by_contra fun hnor ↦
      have ⟨s_ne_empty, s_ne_univ⟩ := not_or.mp hnor
      nonempty_inter s_open sc_open s.union_compl_self
        (Set.nonempty_iff_ne_empty.mpr s_ne_empty)
        (Set.nonempty_compl.mpr s_ne_univ)
        |>.not_disjoint disjoint_compl_right
    mpr := Or.rec (·.substr isClopen_empty) (·.substr isClopen_univ)
  }
  mpr hX := .mk fun A B AO BO hAUB hA hB ↦ (A∩B).univ_inter.substr <|
    have : Bᶜ ⊆ A := fun _ ↦ hAUB trivial |>.resolve_right
    match this.eq_or_ssubset with
    | .inl h =>
      have : IsClopen B := ⟨⟨h.substr AO⟩, BO⟩
      have : B = .univ := hX.mp this |>.resolve_left hB.right.ne_empty
      this.substr <| hA.imp fun _ ↦ .symm
    | .inr h => Set.ssubset_iff_of_subset this |>.mp h |>.imp fun _ ↦ .imp_right not_not.mp

example {a: ℝ} : IsOpen (.Ioi a) := Metric.isOpen_iff.mpr fun x hx ↦
  ⟨x - a, sub_pos_of_lt hx, fun b hb ↦ sub_lt_sub_iff_left x |>.mp <|
    le_abs_self _ |>.trans_eq (dist_comm x b) |>.trans_lt hb ⟩

open TopologicalSpace in
open scoped Topology in
example : OrderTopology ℝ := .mk <| eq_of_le_of_le
  (le_generateFrom fun _ ⟨_a, ha⟩ ↦ ha.elim (· ▸ isOpen_Ioi) (· ▸ isOpen_Iio))
  fun A h ↦
    have hA {x} := Metric.isOpen_iff.mp h x
    let t := generateFrom {s | ∃ a, s = Set.Ioi a ∨ s = Set.Iio a}
    have isOpen_t_ball {x ε : ℝ} : IsOpen[t] (Metric.ball x ε) :=
      x.ball_eq_Ioo ε ▸ .inter (.basic _ ⟨_, .inl rfl⟩) (.basic _ ⟨_, .inr rfl⟩)
    let O := {Metric.ball x (hA hx).choose | (x) (hx: x ∈ A)}
    have UO_isOpen_t := GenerateOpen.sUnion O fun _ ⟨_x, _, hx⟩ ↦ hx.subst isOpen_t_ball
    have A_eq_U0O : A = ⋃₀O := Set.ext fun x ↦ {
      mp := fun hx ↦ ⟨_, ⟨x, hx, rfl⟩, Metric.mem_ball_self (hA hx).choose_spec.left⟩
      mpr := fun ⟨_, ⟨_y, hy, rfl⟩, hx⟩ ↦ (hA hy).choose_spec.right hx
    }
    A_eq_U0O.substr UO_isOpen_t

variable {α} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
         {f g: X → α} {s: Set X} {a b : X}

-- `IsPreconnected.intermediate_value`
example (hs: IsPreconnected s) (a_mem : a ∈ s) (b_mem : b ∈ s) (hf: ContinuousOn f s)
  : Set.Icc (f a) (f b) ⊆ f '' s := fun y ⟨fa_le, y_le⟩ ↦
  let ⟨_y₁, ⟨hy₁, ⟨y₁_le, y₁_ge⟩⟩⟩ := isPreconnected_closed_iff.mp (hs.image f hf)
    (.Iic y) (.Ici y) isClosed_Iic isClosed_Ici
    (Set.subset_univ _ |>.trans_eq Set.Iic_union_Ici.symm)
    ⟨f a, ⟨⟨a, ⟨a_mem, rfl⟩⟩, fa_le⟩⟩
    ⟨f b, ⟨⟨b, ⟨b_mem, rfl⟩⟩, y_le⟩⟩
  eq_of_le_of_le y₁_ge y₁_le |>.substr hy₁

example [PreconnectedSpace X] (hf: Continuous f) (hg: Continuous g) (ha: f a ≤ g a) (hb: g b ≤ f b) :
  ∃x, f x = g x :=
  let yl := g a ⊓ g b
  let yu := g a ⊔ g b
  let ⟨y, ⟨x, True.intro, hx⟩, y_le, y_ge⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_univ.image f hf.continuousOn)
    (.Iic yu) (.Ici yl) isClosed_Iic isClosed_Ici
    (Set.subset_univ _ |>.trans_eq (Set.Iic_union_Ici_of_le inf_le_sup).symm)
    ⟨_, ⟨a, trivial, rfl⟩, ha.trans le_sup_left⟩
    ⟨_, ⟨b, trivial, rfl⟩, inf_le_right.trans hb⟩
  -- have hga : g a ∈ g '' Set.univ := ⟨a, trivial, rfl⟩
  -- have hgb : g b ∈ g '' Set.univ := ⟨b, trivial, rfl⟩
  -- let ⟨y1, ⟨x1, True.intro, hx1⟩, hy1⟩ := isPreconnected_closed_iff.mp
  --   (isPreconnected_univ.image g hg.continuousOn)
  --   (.Iic y) (.Ici y) isClosed_Iic isClosed_Ici
  --   (Set.subset_univ _ |>.trans_eq Set.Iic_union_Ici.symm)
  --   ⟨yl, @inf_ind _ _ _ _ (g '' Set.univ).Mem hga hgb, y_ge⟩
  --   ⟨yu, @sup_ind _ _ _ _ (g '' Set.univ).Mem hga hgb, y_le⟩
  -- let (rfl) : y = y1 := le_antisymm hy1.right hy1.left; clear% hy1
  sorry

-- `IsPreconnected.intermediate_value₂`
example (hs: IsPreconnected s) (hf: ContinuousOn f s) (hg: ContinuousOn g s)
  (a_mem : a ∈ s) (b_mem : b ∈ s) (ha: f a ≤ g a) (hb: g b ≤ f b) : ∃x ∈ s, f x = g x :=
  let yl := g a ⊓ g b
  let yu := g a ⊔ g b

  let ⟨y, ⟨⟨x, hx⟩, ⟨y_le, y_ge⟩⟩⟩ := isPreconnected_closed_iff.mp (hs.image f hf)
    (.Iic yu) (.Ici yl) isClosed_Iic isClosed_Ici
    (Set.subset_univ _ |>.trans_eq (Set.Iic_union_Ici_of_le inf_le_sup).symm)
    ⟨f a, ⟨⟨a, ⟨a_mem, rfl⟩⟩, ha.trans le_sup_left⟩⟩
    ⟨f b, ⟨⟨b, ⟨b_mem, rfl⟩⟩, inf_le_right.trans hb⟩⟩
  have hga : g a ∈ g '' s := ⟨a, a_mem, rfl⟩
  have hgb : g b ∈ g '' s := ⟨b, b_mem, rfl⟩
  let ⟨y1, ⟨x1, hx1⟩, hy1⟩ := isPreconnected_closed_iff.mp (hs.image g hg)
    (.Iic y) (.Ici y) isClosed_Iic isClosed_Ici
    (Set.subset_univ _ |>.trans_eq Set.Iic_union_Ici.symm)
    ⟨yl, @inf_ind _ _ _ _ (g '' s).Mem hga hgb, y_ge⟩
    ⟨yu, @sup_ind _ _ _ _ (g '' s).Mem hga hgb, y_le⟩
  let (rfl) : y = y1 := le_antisymm hy1.right hy1.left; clear% hy1
  ⟨x1, hx1.left, sorry⟩
