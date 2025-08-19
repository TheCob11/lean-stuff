import Mathlib

lemma Finset.mem_pair [DecidableEq α] : x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by
  simp only [mem_insert, mem_singleton]

structure Nation (P G: Type*) (card: ℕ) where
  fav : P → Finset G
  fav_card : ∀p, (fav p).card = card
  fav_ne : Pairwise (Ne on fav)
  fav_common : ∀p₁ p₂, ¬Disjoint (fav p₁) (fav p₂)

namespace Nation
variable {P G} {card} (N: Nation P G card)

def IsSufficient (s: Finset G) : Prop := ∀p, ¬Disjoint s (N.fav p)

theorem not_isSufficient_empty [inst: Nonempty P] : ¬N.IsSufficient ∅ := inst.elim fun p h ↦
  h p (N.fav p).disjoint_empty_left

theorem isSufficient_empty_iff_isEmpty : N.IsSufficient ∅ ↔ IsEmpty P where
  mp h := not_nonempty_iff.mp fun _ ↦ N.not_isSufficient_empty h
  mpr h := h.elim

theorem fav_nonempty p : (N.fav p).Nonempty := Finset.nonempty_of_ne_empty fun h ↦
  h ▸ N.fav_common p p <| Finset.disjoint_empty_left ∅

theorem n_pos [inst: Nonempty P] : 0 < card := inst.elim fun p ↦
  N.fav_card p |>.subst <| N.fav_nonempty p |>.card_pos

theorem isSufficient_fav (p) : N.IsSufficient (N.fav p) := N.fav_common p

-- def favPool (N: Nation P G) : Finset G := sorry

-- theorem card_favPool : N.favPool.card = N.card - 1 := sorry

-- theorem isSufficient_favPool : N.IsSufficient N.favPool := sorry

-- this sucks
theorem exists_sufficient_single [Infinite P] [DecidableEq P] [DecidableEq G] (N: Nation P G 2) :
  ∃g, ∀p, g ∈ N.fav p := by_contra fun hnex: ¬∃g, ∀p, g ∈ N.fav p ↦
  let ⟨p, q, p_ne_q⟩ := Infinite.instNontrivial P
  let ⟨gpq, ⟨hgpqp, hgpqq⟩⟩ := Finset.not_disjoint_iff.mp <| N.fav_common p q

  let ⟨gp, gp_mem, gp_ne⟩ := Finset.exists_ne_of_one_lt_card (N.fav_card p |>.substr one_lt_two) gpq
  let ⟨gq, gq_mem, gq_ne⟩ := Finset.exists_ne_of_one_lt_card (N.fav_card q |>.substr one_lt_two) gpq

  have fav_p_eq : N.fav p = {gpq, gp} := Eq.symm <| Finset.eq_of_subset_of_card_le
    (fun g hg ↦ Finset.mem_pair.mp hg |>.elim (fun | rfl => hgpqp) (fun | rfl => gp_mem))
    (N.fav_card p |>.substr <| Nat.le_of_eq (Finset.card_pair gp_ne.symm).symm)
  have fav_q_eq : N.fav q = {gpq, gq} := Eq.symm <| Finset.eq_of_subset_of_card_le
    (fun g hg ↦ Finset.mem_pair.mp hg |>.elim (fun | rfl => hgpqq) (fun | rfl => gq_mem))
    (N.fav_card q |>.substr <| Nat.le_of_eq (Finset.card_pair gq_ne.symm).symm)

  have gp_ne_gq : gp ≠ gq := fun | rfl => N.fav_ne p_ne_q <| fav_p_eq.trans fav_q_eq.symm

  let ⟨r, hr⟩ : ∃p, gpq ∉ N.fav p := by_contra fun h ↦ hnex ⟨gpq, not_exists_not.mp h⟩
  have gp_mem_fr : gp ∈ N.fav r :=
    have ⟨g, ⟨g_mem_fp, g_mem_rp⟩⟩ := Finset.not_disjoint_iff.mp <| N.fav_common p r
    have : g = gpq ∨ g = gp := Finset.mem_pair.mp <| fav_p_eq.subst g_mem_fp
    this.resolve_left (fun | rfl => hr g_mem_rp) ▸ g_mem_rp
  have gq_mem_fr : gq ∈ N.fav r :=
    have ⟨g, ⟨g_mem_fq, g_mem_rp⟩⟩ := Finset.not_disjoint_iff.mp <| N.fav_common q r
    have : g = gpq ∨ g = gq := Finset.mem_pair.mp <| fav_q_eq.subst g_mem_fq
    this.resolve_left (fun | rfl => hr g_mem_rp) ▸ g_mem_rp
  have fav_r_eq : N.fav r = {gp, gq} := Eq.symm <| Finset.eq_of_subset_of_card_le
    (fun g hg ↦ Finset.mem_pair.mp hg |>.elim (fun | rfl => gp_mem_fr) (fun | rfl => gq_mem_fr))
    (N.fav_card r |>.substr <| Nat.le_of_eq (Finset.card_pair gp_ne_gq).symm)

  let ⟨s, s_nin⟩ : ∃s, s ∉ ({p, q, r}: Finset P) := Infinite.exists_not_mem_finset {p, q, r}
  have ⟨s_ne_p, s_ne_q, s_ne_r⟩ : s ≠ p ∧ s ≠ q ∧ s ≠ r := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using s_nin
  if hs: gpq ∈ N.fav s then
    let ⟨g, ⟨hgr, hgs⟩⟩ := Finset.not_disjoint_iff.mp <| N.fav_common r s
    have g_eq : g = gp ∨ g = gq := Finset.mem_pair.mp <| fav_r_eq.subst hgr
    have g_ne : g ≠ gpq := g_eq.elim (fun | rfl => gp_ne) (fun | rfl => gq_ne)
    have fav_s_eq : N.fav s = {gpq, g} := Eq.symm <| Finset.eq_of_subset_of_card_le
      (fun g hg ↦ Finset.mem_pair.mp hg |>.elim (fun | rfl => hs) (fun | rfl => hgs))
      (N.fav_card s |>.substr <| Nat.le_of_eq (Finset.card_pair g_ne.symm).symm)
    match g_eq with
    | .inl rfl => N.fav_ne s_ne_p <| fav_s_eq.trans fav_p_eq.symm
    | .inr rfl => N.fav_ne s_ne_q <| fav_s_eq.trans fav_q_eq.symm
  else
    let ⟨g₁, ⟨hg₁p, hg₁s⟩⟩ := Finset.not_disjoint_iff.mp <| N.fav_common p s
    have g₁_ne : g₁ ≠ gpq := fun | rfl => hs hg₁s
    have g₁_eq : g₁ = gp := (Finset.mem_pair.mp <| fav_p_eq.subst hg₁p).resolve_left g₁_ne
    let ⟨g₂, ⟨hg₂q, hg₂s⟩⟩ := Finset.not_disjoint_iff.mp <| N.fav_common q s
    have g₂_eq : g₂ = gq := (Finset.mem_pair.mp <| fav_q_eq.subst hg₂q).resolve_left
      fun | rfl => hs hg₂s
    have fav_s_eq : N.fav s = {gp, gq} := Eq.symm <| Finset.eq_of_subset_of_card_le
      (fun g hg ↦ Finset.mem_pair.mp hg |>.elim
        (fun | rfl => g₁_eq ▸ hg₁s) (fun | rfl => g₂_eq ▸ hg₂s))
      (N.fav_card s |>.substr <| Nat.le_of_eq (Finset.card_pair gp_ne_gq).symm)
    N.fav_ne s_ne_r <| fav_s_eq.trans fav_r_eq.symm

theorem exists_isSufficient_card_sub_one [Infinite P] [DecidableEq P] [DecidableEq G]
  (hcard: 2 ≤ card) : ∃s, N.IsSufficient s ∧ s.card = card - 1 := by
  induction card, hcard using Nat.le_induction
  case base => exact
    let ⟨g, hg⟩ := exists_sufficient_single N
    let s: Finset G := {g}
    have hs : N.IsSufficient s := fun p ↦ Finset.not_disjoint_iff.mpr
      ⟨g, ⟨Finset.mem_singleton_self g, hg p⟩⟩
    ⟨s, ⟨hs, Finset.card_singleton s⟩⟩
  case succ ih =>
    sorry
