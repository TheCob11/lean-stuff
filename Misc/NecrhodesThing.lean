import Mathlib

section ConstructiveSetLemmas

-- `Set.iInter_of_empty` without axiom of choice, still needs propext and Quot.sound
lemma iInter_of_empty [IsEmpty ι] (U: ι → Set α) : ⋂i, U i = Set.univ :=
  Set.ext fun _ ↦ {
    mp := fun _ ↦ trivial
    mpr := fun _ _ ⟨i, _⟩ ↦ isEmptyElim i
  }

/-- info: 'iInter_of_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms iInter_of_empty

-- `Set.iInter_of_empty` without axiom of choice, still needs propext and Quot.sound
lemma iUnion_of_empty [IsEmpty ι] (U: ι → Set α) : ⋃i, U i = ∅ :=
  Set.ext fun _ ↦ {
    mp := fun ⟨_, ⟨⟨i, _⟩, _⟩⟩ ↦ isEmptyElim i
    mpr := False.elim
  }

/-- info: 'iUnion_of_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms iUnion_of_empty

-- like `Set.inter_eq_iInter` w/o choice
lemma iInter_eq_inter : ⋂ b, cond b s₁ s₂ = s₁ ∩ s₂ := Set.ext fun _ ↦
  Set.mem_iInter.trans {
    mp := fun h ↦ ⟨h true, h false⟩
    mpr := fun h c ↦ c.casesOn h.right h.left
  }

/-- info: 'iInter_eq_inter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms iInter_eq_inter

lemma singleton_inter_singleton_eq_empty (a b : α) : {a} ∩ {b} = (∅: Set α) ↔ a ≠ b where
  -- mp h := fun hne ↦ by simp_all only [Set.inter_self, Set.singleton_ne_empty]
  mp h := fun (.refl _) ↦
    have : a ∈ ({a} ∩ {a}: Set α) := ⟨rfl, rfl⟩
    h.subst this
  mpr hne := Set.ext fun _ ↦ {
    mp := fun | ⟨rfl, rfl⟩ => hne rfl
    mpr := False.elim
  }

/-- info: 'singleton_inter_singleton_eq_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms singleton_inter_singleton_eq_empty

lemma not_nonempty_iff_eq_empty (s: Set α) : ¬s.Nonempty ↔ s = ∅ where
  mp hn := s.eq_empty_of_forall_not_mem fun x hx ↦ hn ⟨x, hx⟩
  mpr h := h.substr Set.not_nonempty_empty


/-- info: 'not_nonempty_iff_eq_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_nonempty_iff_eq_empty

end ConstructiveSetLemmas

/-
one of the worst parts of doing this all constructively is that I can't use
`CompleteLatticeHom (Set S) (Set G)` to contain everything because the relevant
API uses choice a bunch >:(
-/
-- like `CompleteLatticeHom (Set α) (Set β)` but constructive
structure CSetCompleteLatticeHom (α β) where
  toFun : Set α → Set β
  map_sUnion' (U: Set (Set α)) : toFun U.sUnion = (toFun '' U).sUnion
  map_sInter' (U: Set (Set α)) : toFun U.sInter = (toFun '' U).sInter

variable {S G : Type*} (φ: CSetCompleteLatticeHom S G)

namespace CSetCompleteLatticeHom

instance : FunLike (CSetCompleteLatticeHom α β) (Set α) (Set β) where
  coe f := f.toFun
  coe_injective' := fun | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem map_iInter (U: ι → Set S) : φ (⋂i, U i) = ⋂i, φ (U i) :=
  φ.map_sInter' (Set.range U) |>.trans <| Set.ext fun _ ↦ {
    mp :=  fun h y ⟨i, hi⟩ ↦ h y ⟨U i, ⟨⟨i, rfl⟩, hi⟩⟩
    mpr := fun h y ⟨_x, ⟨⟨i, hi⟩, hx⟩⟩ ↦ h y ⟨i, hx ▸ hi ▸ rfl⟩
  }

/-- info: 'CSetCompleteLatticeHom.map_iInter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms map_iInter

theorem map_iUnion (U: ι → Set S) : φ (⋃i, U i) = ⋃i, φ (U i) :=
  φ.map_sUnion' (Set.range U) |>.trans <| Set.ext fun _ ↦ {
    mp := .imp fun _y ⟨⟨_x, ⟨⟨i, hi⟩, hx⟩⟩, hy⟩ ↦ ⟨⟨i, hx ▸ hi ▸ rfl⟩, hy⟩
    mpr := .imp fun _y ⟨⟨i, hi⟩, hy⟩ ↦ ⟨⟨U i, ⟨⟨i, rfl⟩, hi⟩⟩, hy⟩
  }

/-- info: 'CSetCompleteLatticeHom.map_iUnion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms map_iUnion

theorem map_univ : φ Set.univ = Set.univ :=
  iInter_of_empty (fun _: Empty ↦ ∅) |>.symm.substr <|
    (φ.map_iInter (fun _: Empty ↦ ∅) |>.trans <| iInter_of_empty _)

/-- info: 'CSetCompleteLatticeHom.map_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms map_univ

theorem map_empty : φ ∅ = ∅ :=
  iUnion_of_empty (fun _: Empty ↦ ∅) ▸ φ.map_iUnion _ |>.trans <| iUnion_of_empty _

/-- info: 'CSetCompleteLatticeHom.map_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms map_empty

example {f : α → β} : f (cond b x y) = cond b (f x) (f y) := Bool.apply_cond f

theorem map_inter : φ (s ∩ t) = φ s ∩ φ t := calc
  _ = φ (⋂b, cond b s t) := iInter_eq_inter.substr rfl
  _ = ⋂b, φ (cond b s t) := φ.map_iInter _
  _ = ⋂b, cond b (φ s) (φ t) := by simp_rw [Bool.apply_cond φ]
  _ = _ := iInter_eq_inter

/-- info: 'CSetCompleteLatticeHom.map_inter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms map_inter

end CSetCompleteLatticeHom

def f: Rel G S := fun g s ↦ g ∈ φ {s}

theorem f_total (g: G) : ∃s, f φ g s :=
  have : Set.univ = ⋃s: S, φ {s} := calc
    _ = φ Set.univ := φ.map_univ.symm
    _ = φ (⋃s: S, {s}) := Set.iUnion_of_singleton S |>.substr rfl
    _ = ⋃s: S, φ {s} := φ.map_iUnion _
  let ⟨_, ⟨⟨s, rfl⟩, hs⟩⟩ := Set.ext_iff.mp this g |>.mp trivial
  ⟨s, hs⟩

/-- info: 'f_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms f_total

variable {g: G} {s₁ s₂ : S} (hs₁ : f φ g s₁)

theorem f_single_valued_almost (hs₂ : f φ g s₂) : ¬s₁ ≠ s₂ :=
  have : g ∈ φ ({s₁} ∩ {s₂}) := φ.map_inter.substr ⟨hs₁, hs₂⟩
  have : {s₁} ∩ {s₂} ≠ (∅: Set _) := fun h ↦ φ.map_empty.subst <| h ▸ this
  singleton_inter_singleton_eq_empty s₁ s₂ |>.not.mp this

/-- info: 'f_single_valued_almost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms f_single_valued_almost

theorem f_single_valued_classical [DecidableEq S] (hs₂ : f φ g s₂) : s₁ = s₂ :=
  Decidable.eq_or_ne s₁ s₂ |>.resolve_right <| f_single_valued_almost φ hs₁ hs₂

/-- info: 'f_single_valued_classical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms f_single_valued_classical

theorem f_single_valued_iff_not_not_eq : f φ g s₂ ↔ ¬s₁ ≠ s₂ where
  mp := f_single_valued_almost φ hs₁
  mpr h :=
    have : {s₁} ∩ {s₂} ≠ ∅ := singleton_inter_singleton_eq_empty s₁ s₂ |>.not.mpr h
    have hs₁ : g ∈ φ {s₁} := hs₁

    sorry

/-- info: 'f_single_valued_iff_not_not_eq' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in
#print axioms f_single_valued_iff_not_not_eq
