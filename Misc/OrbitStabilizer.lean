import Mathlib
open MulAction
theorem orbit_stabilizer (G : Type u) {S : Type v} [Group G] [MulAction G S] (s: S) :
  Subgroup.index (stabilizer G s) = Nat.card (orbit G s) := by

  unfold Subgroup.index
  let G_quo_stab := G ⧸ stabilizer G s;
  let φ (xStab : G_quo_stab) : orbit G s :=
    ⟨xStab.exists_rep.choose • s, mem_orbit _ _⟩
  have φ_Bij : Function.Bijective φ := by
    have smul_s_eq_iff_coset_eq {x: G} {y: G} : (x•s = y•s) ↔ @Eq G_quo_stab ⟦x⟧ ⟦y⟧ := by
      rw [smul_eq_iff_eq_inv_smul, Eq.comm, smul_smul]
      rw [← mem_stabilizer_iff]
      rw [← QuotientGroup.leftRel_apply, ← @Quotient.eq', @Quotient.mk'_eq_mk]
    have coset_choose (x: G_quo_stab) := x.exists_rep.choose_spec;
    have φ_Surj : Function.Surjective φ := by
      -- this proof feels kinda clunky but idk how else to do it
      simp [φ, Function.Surjective]
      intro s' hs'
      obtain ⟨x, hx⟩ := Set.mem_range.mpr hs'
      rw [QuotientGroup.exists_mk]
      use x
      rw [← hx]
      rw [smul_s_eq_iff_coset_eq]
      rw [coset_choose x]
      rfl
    have φ_Inj : Function.Injective φ := by
      simp [φ, Function.Injective]
      intro xStab yStab h
      rw [smul_s_eq_iff_coset_eq] at h
      rwa [coset_choose xStab, coset_choose yStab] at h
    exact ⟨φ_Inj, φ_Surj⟩
  exact Nat.card_eq_of_bijective φ φ_Bij
