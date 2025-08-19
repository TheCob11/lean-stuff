import Mathlib
variable {α: Type u} [Preorder α]

open Order in
theorem zorn [DecidablePred <| @IsChain α (· ≤ ·)]
  (hchain: ∀{c: Set α}, IsChain (· ≤ ·) c → BddAbove c) : ∃a: α, IsMax a :=
  by_contra fun hnex ↦
  have hbig : ∀a, ∃b, a < b := not_isMax_iff.mp ∘' not_exists.mp hnex
  clear% hnex
  have hchain_lt {c: Set α} (hc: IsChain (· ≤ ·) c) : ∃b, ∀{a}, a ∈ c → a < b :=
    have ⟨ub, hub⟩ := hchain hc
    let ⟨b, hb⟩ := hbig ub
    ⟨b, fun ha ↦ hub ha |>.trans_lt hb⟩
  clear% hbig
  let a0 : α := hchain .empty |>.choose
  let f (c: Set α) : α := if h: IsChain (· ≤ ·) c then hchain_lt h |>.choose else a0
  have hf {c} (hc: IsChain (· ≤ ·) c) : ∀{a}, a ∈ c → a < f c := fun ha ↦
    congrArg _ (dif_pos hc) |>.mpr <| (hchain_lt hc).choose_spec ha
  let A : Ordinal.{u} → α := Ordinal.lt_wf.fix fun i hi ↦ f {hi j hj | (j) (hj: j < i)}
  have hA_eq o : f (A '' .Iio o) = A o := .symm <| calc
    _ = f {A j | (j) (_: j < o)} := WellFounded.fix_eq _ _ o
    _ = f (A '' .Iio o) := congrArg f <| Set.ext fun _ ↦ {
      mp | ⟨j, j_lt, hj⟩ => ⟨j, j_lt, hj⟩
      mpr | ⟨j, j_lt, hj⟩ => ⟨j, j_lt, hj⟩
    }
  have hAchain o : IsChain (· ≤ ·) (A '' .Iio o) := o.limitRecOn
    (Set.Iio_bot.substr <| Set.image_empty A |>.substr IsChain.empty)
    (fun i ih ↦
      have : A '' Set.Iio (succ i) = insert (A i) (A '' Set.Iio i) :=
        Iio_succ_eq_insert i |>.substr Set.image_insert_eq
      this ▸ IsChain.insert ih fun _ ha _ ↦ .inr <| (hf ih ha).trans_eq (hA_eq i) |>.le)
    fun _i hi ih _a ⟨ja, ja_lt, hja⟩ _b ⟨jb, jb_lt, hjb⟩ ↦
      let j := ja ⊔ jb
      ih (succ j) (hi.succ_lt (sup_lt_iff.mpr ⟨ja_lt, jb_lt⟩))
        ⟨ja, le_sup_left.trans_lt (lt_succ j), hja⟩
        ⟨jb, le_sup_right.trans_lt (lt_succ j), hjb⟩
  have hA : StrictMono A := fun i j h ↦ hA_eq j ▸ hf (hAchain j) ⟨i, h, rfl⟩
  open Cardinal in (
  have : univ.{u, u+1} ≤ lift.{u+1} (.mk α) := calc
    _ = lift.{u} (univ.{u, u+1}) := lift_univ.symm
    _ = lift.{u} (.mk Ordinal.{u}) := congrArg _ univ_id.{u}
    _ ≤ _ := lift_mk_le_lift_mk_of_injective hA.injective
  lift_lt_univ (.mk α) |>.not_le this)
