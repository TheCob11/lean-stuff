import Mathlib
open Topology

-- example {a b : ℝ} : IsPreconnected (Set.Ioo a b) := fun U V hU hV hUV U_nemp V_nemp ↦ by
--   let I := Set.Ioo a b
--   -- wlog h1V : b ∈ V generalizing U V
--   -- · rw [U.inter_comm V, U.union_comm V] at *
--   --   exact this V U hV hU hUV V_nemp U_nemp <| hUV sorry |>.resolve_left h1V
--   wlog hU_subs : U ⊆ I generalizing U
--   · let UI := I ∩ U
--     have hUIV : I ⊆ UI ∪ V := fun t ht ↦ hUV ht |>.imp_left (⟨ht, ·⟩)
--     let ⟨u, huI, ⟨_, huU⟩, huV⟩ := this UI (isOpen_Ioo.inter hU) hUIV
--       (U_nemp.imp fun _ ⟨htI, htU⟩ ↦ ⟨htI, htI, htU⟩) inf_le_left
--     exact ⟨u, huI, huU, huV⟩
--   let x := sSup U
--   have hbupU : b ∈ upperBounds U := fun u hu ↦ hU_subs hu |>.right.le
--   have bdd_U : BddAbove U := ⟨b, hbupU⟩
--   let ⟨u, huI, huU⟩ := U_nemp
--   have : x ∈ Set.Ioc a b := ⟨huI.1.trans_le <| le_csSup bdd_U huU, csSup_le U_nemp.right hbupU⟩

--   sorry

open unitInterval

-- example : IsPreconnected I := isPreconnected_closed_iff.mpr fun U V hU hV hUV U_nemp V_nemp ↦ by
--   wlog hU_subs : U ⊆ Set.Icc 1 1 generalizing U
--   ·
--     let S: Set ℝ := Set.Icc 1 1
--     let UI := S ∩ U
--     have hUSV : S ⊆ UI ∪ V := fun t ht ↦ hUV ⟨zero_le_one.trans ht.1, ht.2⟩ |>.imp_left (⟨ht, ·⟩)
--     have hUIV : I ⊆ UI ∪ V := fun t ht ↦ hUV ht |>.imp_left fun htU ↦ (⟨sorry, htU⟩)
--     let ⟨u, huI, ⟨_, huU⟩, huV⟩ := this UI (isClosed_Icc.inter hU) hUIV
--       (U_nemp.imp fun _ ⟨htI, htU⟩ ↦ ⟨htI, htI, htU⟩) inf_le_left
--     exact ⟨u, huI, huU, huV⟩

--   sorry

-- example : IsConnected I := .intro .of_subtype <| isPreconnected_closed_iff.mpr
--   fun U V hU hV hUV U_nemp V_nemp ↦ by
--   wlog hone : 1 ∈ U generalizing U V
--   · exact U.inter_comm V |>.substr <| this V U hV hU (U.union_comm V ▸ hUV) V_nemp U_nemp <|
--       hUV (1: I).prop |>.resolve_left hone
--   let v := sSup V
--   -- have : v ∈ closure V := Metric.mem_closure_iff.mpr fun ε ε_pos ↦ .intro (v - ε/2)
--   --   sorry
--   sorry

example : PreconnectedSpace I := .mk fun U V hU hV hUV U_nemp V_nemp ↦ (U ∩ V).univ_inter.symm ▸ by
  -- wlog hone : 1 ∈ U generalizing U V
  -- · exact U.inter_comm V ▸ this V U hV hU (U.union_comm V ▸ hUV) V_nemp U_nemp <|
  --     hUV trivial |>.resolve_left hone
  refine Set.not_disjoint_iff_nonempty_inter.mp fun hdisj ↦ ?_
  have : U = Vᶜ := eq_compl_iff_isCompl.mpr ⟨hdisj, codisjoint_iff_le_sup.mpr hUV⟩
  subst this
  clear hdisj hUV
  replace hU : IsClosed V := ⟨hU⟩
  -- obtain ⟨u, _, hu⟩ := U_nemp
  -- obtain ⟨v, _, hv⟩ := V_nemp
  -- wlog unga: sSup V ∈ Vᶜ generalizing V
  -- · have := this Vᶜ
  --   rw [compl_compl V] at this
  --   exact this hU.1 U_nemp V_nemp hV.isClosed_compl sorry
  let x := sSup V
  have x_mem_closure : x ∈ closure V := Metric.mem_closure_iff.mpr fun ε ε_pos ↦ .intro
    (Set.projIcc 0 1 zero_le_one (x.val - ε/2))
    (.intro sorry sorry)
  if hx: x ∈ V then
    sorry
  else
  have : x ∉ closure V := hU.closure_eq.substr hx
  -- have := Metric.mem_closure_iff.not.mp this
  -- push_neg at this

  sorry

section
variable {α} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {S: Set α} {a: α}

-- `IsLUB.mem_closure`
example (ha: IsLUB S a) (hS: S.Nonempty) : a ∈ closure S := mem_closure_iff_nhds.mpr fun _U hU ↦
  let ⟨s, hs⟩ := hS; clear% hS
  if hsa : s = a then ⟨a, mem_of_mem_nhds hU, hsa.subst hs⟩ else
  have : s < a := ha.1 hs |>.lt_of_ne hsa; clear% hsa
  let ⟨_l, l_lt_a, hlU⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨s, this⟩
  let ⟨b, hbS, hbl⟩ := lt_isLUB_iff ha |>.mp l_lt_a
  ⟨b, hlU ⟨hbl, ha.1 hbS⟩, hbS⟩

example (ha: IsLUB S a) (a_mem: a ∈ S) : IsGreatest S a := ⟨a_mem, ha.1⟩

theorem IsGreatest.mem_closure_compl [DenselyOrdered α] (haS: IsGreatest S a) (hb: ∃b, a < b) :
  a ∈ closure (Sᶜ) := mem_closure_iff_nhds.mpr fun _U hU ↦
  let ⟨_c, a_lt_c, hcU⟩ := exists_Ico_subset_of_mem_nhds hU hb
  let ⟨b, b_gt, b_lt⟩ := exists_between a_lt_c
  ⟨b, hcU ⟨b_gt.le, b_lt⟩, b_gt.not_le.imp (haS.2 ·)⟩

end

example : PreconnectedSpace I := .mk <| isPreconnected_closed_iff.mpr
  fun U V hU hV hUV U_nemp V_nemp ↦ Set.univ_inter _ ▸ Set.not_disjoint_iff_nonempty_inter.mp
  fun hdisj ↦
  let (rfl) : Vᶜ = U := IsCompl.eq_compl ⟨hdisj, codisjoint_iff_le_sup.mpr hUV⟩ |>.symm
  clear% hdisj; clear% hUV
  by
  wlog h1n : ⊤ ∉ V generalizing V
  · exact this Vᶜ hU U_nemp (compl_compl V |>.substr hV) (compl_compl V |>.substr V_nemp) h1n
  exact
  let x := sSup V
  have hxV : x ∈ V := isLUB_sSup V |>.mem_of_isClosed V_nemp.right hV
  have : IsGreatest V x := ⟨hxV, fun _ ↦ le_sSup⟩
  have hxU : x ∈ Vᶜ := hU.closure_eq ▸ this.mem_closure_compl ⟨⊤, Ne.lt_top <| h1n.imp (· ▸ hxV)⟩
  hxU hxV

example : PreconnectedSpace (@Set.Ioo ℝ _ 0 1) := .mk <| isPreconnected_closed_iff.mpr <| by
  rintro U V hU hV hUV ⟨u, -, hu⟩ ⟨v, -, hv⟩
  refine Set.univ_inter _ ▸ Set.not_disjoint_iff_nonempty_inter.mp fun hdisj ↦ ?_
  let (rfl) : Vᶜ = U := IsCompl.eq_compl ⟨hdisj, codisjoint_iff_le_sup.mpr hUV⟩ |>.symm
  clear hdisj; clear hUV
  -- by
  wlog v_le: v ≤ u generalizing u v V
  · exact this Vᶜ hU v u hu ((compl_compl V).substr hV) ((compl_compl V).substr hv) (le_of_not_le v_le)
  wlog V_le: V ⊆ .Iic v generalizing V
  · let VI := V ∩ .Iic v

    exact this VI (hV.inter isClosed_Iic) ⟨hv, le_refl v⟩ sorry (hu.imp And.left) V.inter_subset_right
  sorry

example : IsPreconnected I := isPreconnected_closed_iff.mpr fun U V hU hV hUV U_nemp V_nemp ↦ by
  wlog h1V : 1 ∈ V generalizing U V
  · rw [U.inter_comm V, U.union_comm V] at *
    exact this V U hV hU hUV V_nemp U_nemp <| hUV one_mem |>.resolve_left h1V
  -- wlog h0U : 0 ∈ U generalizing U V
  -- · rw [U.inter_comm V, U.union_comm V] at *
  --   exact this V U hV hU hUV V_nemp U_nemp <| hUV zero_mem |>.resolve_right h0U
  wlog hU_subs : U ⊆ I generalizing U
  · let UI := I ∩ U
    have hUIV : I ⊆ UI ∪ V := fun t ht ↦ hUV ht |>.imp_left (⟨ht, ·⟩)
    let ⟨u, huI, ⟨_, huU⟩, huV⟩ := this UI (isClosed_Icc.inter hU) hUIV
      (U_nemp.imp fun _ ⟨htI, htU⟩ ↦ ⟨htI, htI, htU⟩) inf_le_left
    exact ⟨u, huI, huU, huV⟩
  if h1U : 1 ∈ U then exact ⟨1, one_mem, h1U, h1V⟩ else
  let x := sSup U
  have h1upU : 1 ∈ upperBounds U := fun u hu ↦ hU_subs hu |>.right
  let ⟨u, huI, huU⟩ := U_nemp
  have bdd_U : BddAbove U := ⟨1, h1upU⟩
  have hxI : x ∈ I := ⟨huI.1.trans <| le_csSup bdd_U huU, csSup_le U_nemp.right h1upU⟩
  refine ⟨x, hxI, ?_⟩
  if hxU : x ∈ U then exact
    have : x ≠ 1 := fun h ↦ h1U <| h ▸ hxU
    have : x ∈ V := Metric.mem_of_closed' hV |>.mpr fun ε ε_pos ↦
      let δ := ε/2 ⊓ (1 - x)
      have δ_pos : 0 < δ := lt_inf_iff.mpr ⟨half_pos ε_pos, sub_pos_of_lt <| hxI.2.lt_of_ne this⟩
      let y := x + δ
      have dist_y : dist x y < ε := dist_self_add_right x δ |>.trans_lt <|
        abs_eq_self.mpr δ_pos.le |>.trans_lt <| inf_lt_of_left_lt (half_lt_self ε_pos)
      have hxy : x < y := lt_add_iff_pos_right x |>.mpr δ_pos
      have y_nmem : y ∉ U := not_mem_of_csSup_lt hxy bdd_U
      have : y ∈ I := ⟨hxI.1.trans hxy.le,
        add_inf ..|>.trans_le <| inf_le_of_right_le (add_sub_cancel x 1).le⟩
      ⟨y, hUV this |>.resolve_left y_nmem, dist_y⟩
    ⟨hxU, this⟩
  else exact ⟨isLUB_csSup ⟨u, huU⟩ bdd_U |>.mem_of_isClosed ⟨u, huU⟩ hU, hUV hxI |>.resolve_left hxU⟩

example : PathConnectedSpace ℝ where
  nonempty := ⟨1⟩
  joined x y := Nonempty.intro {
    toFun i := σ i * x + i * y
    continuous_toFun :=
      -- let f: I → ℝ :=
      --   (fun p ↦ p.1 + p.2) ∘
      --   (Prod.map (x * ·) (y * ·)) ∘
      --   (Prod.map (↑) (↑)) ∘
      --   (fun i ↦ (σ i, i))
      continuous_add.comp <|
        (continuous_mul_right x).prodMap (continuous_mul_right y) |>.comp <|
          continuous_subtype_val.prodMap continuous_subtype_val |>.comp <|
            continuous_symm.prodMk continuous_id
    source' := by simp
    target' := by simp
  }

example : PathConnectedSpace (@Metric.sphere (EuclideanSpace ℝ (Fin 2)) _ 0 1) where
  nonempty := ⟨EuclideanSpace.single 0 1,
    mem_sphere_zero_iff_norm.mpr <| EuclideanSpace.norm_single .. |>.trans norm_one⟩
  joined x y :=
  -- Nonempty.intro {
    -- toFun :=
    let unga : @Set.Icc ℝ _ 0 (2 * .pi) := sorry
    let θ₁ := Real.arccos (x.val 0)
    let θ₂ := Real.arccos (y.val 0)
    let s1 θ := !₂[Real.Angle.cos θ, Real.Angle.sin θ]
    have : Continuous s1 := sorry
    let s: C(ℝ, _) := {
      toFun θ := ⟨s1 θ, by simp [s1, EuclideanSpace.sphere_zero_eq]⟩
      continuous_toFun := sorry
    }
    ⟨s.comp <| PathConnectedSpace.somePath θ₁ θ₂, sorry, sorry⟩
  --   continuous_toFun := sorry
  --   source' := sorry
  --   target' := sorry
  -- }

example [Fintype n] [Inhabited n] [DecidableEq n] :
  PathConnectedSpace (@Metric.sphere (EuclideanSpace ℝ n) _ 0 1) where
  nonempty := ⟨EuclideanSpace.single default 1, by simp⟩
  joined x y :=
    let p: C(I, {v : EuclideanSpace ℝ n // v ≠ 0}) := {
      toFun i := ⟨(σ i).val • x.val + i.val • y.val, sorry⟩
      continuous_toFun :=
        -- let f :=
        --   Add.add.uncurry ∘
        --   (Prod.map SMul.smul.uncurry SMul.smul.uncurry) ∘
        --   (Prod.map (·, x.val) (·, y.val)) ∘
        --   (Prod.map Subtype.val Subtype.val) ∘
        --   (fun i ↦ (σ i, i))

        (continuous_add.comp <|
          continuous_smul.prodMap continuous_smul |>.comp <|
            (Continuous.prodMk_left x.val).prodMap (.prodMk_left y.val) |>.comp <|
              continuous_subtype_val.prodMap continuous_subtype_val |>.comp <|
                continuous_symm.prodMk continuous_id).subtype_mk _
    }
    let normalize: C(_, _) := {
      toFun v := ⟨‖v.val‖⁻¹ • v.val, by simp [norm_smul, v.prop]⟩
      continuous_toFun :=
        -- let f :=
        --   SMul.smul.uncurry ∘
        --   (Prod.map (·⁻¹) id) ∘
        --   (fun v ↦ (‖v‖, v)) ∘
        --   Subtype.val
        sorry
        -- Continuous.subtype_mk
        --   (by
        --     refine continuous_smul.comp ?_
        --     refine (continuous_inv).prodMap continuous_id |>.comp ?_
        --     sorry) _
    }
    ⟨normalize.comp p, sorry, sorry⟩
  --       Nonempty.intro {
  --   toFun i :=
  --     let v := (σ i).val • x.val + i.val • y.val
  --     have : v ≠ 0 := sorry
  --     ⟨‖v‖⁻¹ • v, by simp [norm_smul, this]⟩
  --   continuous_toFun :=
  --     (continuous_add.comp <|
  --       continuous_smul.prodMap continuous_smul |>.comp <|
  --         (Continuous.prodMk_left x.val).prodMap (.prodMk_left y.val) |>.comp <|
  --           continuous_subtype_val.prodMap continuous_subtype_val |>.comp <|
  --             continuous_symm.prodMk continuous_id).subtype_mk _
  --   source' := sorry
  --   target' := sorry
  -- }
local notation "ℝ^"n => EuclideanSpace ℝ n
example [Fintype n] [DecidableEq n] [hn: Nontrivial n] :
  IsPathConnected (@Metric.sphere (ℝ^n) _ 0 1) :=
  let S := @Metric.sphere (ℝ^n) _ 0 1
  let normize (v: ℝ^n) : ℝ^n := ‖v‖⁻¹ • v
  have nize_sphere {v} (hv: v ∈ S) : normize v = v := by simp_all [normize, S]
  have hnize : normize '' {0}ᶜ = S := Set.ext fun x ↦ {
    mp | ⟨v, hv, hvx⟩ => by simp [normize, S, ←hvx, norm_smul, norm_ne_zero_iff.mpr hv]
    mpr hx := ⟨normize x, fun _ ↦ by simp_all [normize, S], (nize_sphere hx).symm ▸ nize_sphere hx⟩
  }
  have continuousOn_normize : ContinuousOn normize {0}ᶜ :=
    continuousOn_inv₀.comp continuous_norm.continuousOn (fun _ ↦ norm_ne_zero_iff.mpr) |>.smul continuousOn_id
  let ⟨i, j, hij⟩ := hn
  let a := .single i 1
  have ha : a ∈ S := by simp [a, S]
  let p (x y: ℝ^n) : Path x y := {
    toFun i := (σ i).val • x + i.val • y
    continuous_toFun := continuous_subtype_val.comp continuous_symm |>.smul continuous_const
      |>.add <| continuous_subtype_val.smul continuous_const
    source' := by simp
    target' := by simp
  }
  have p_nz {x y} (hy: y ≠ -x) : Set.range (p x y) ⊆ {0}ᶜ := fun x ⟨t, ht⟩ ↦ by sorry
  let c := .single j 1
  have hz : c ∈ S := by simp [c, S]
  .intro a <| .intro ha @fun b hb ↦
    if hbneg : b = -a then .intro
      { toFun := sorry
        continuous_toFun := sorry
        source' := sorry
        target' := sorry }
      sorry
    else nize_sphere ha ▸ nize_sphere hb ▸ .intro
      (p a b |>.map' <| continuousOn_normize.mono (p_nz hbneg))
      sorry
