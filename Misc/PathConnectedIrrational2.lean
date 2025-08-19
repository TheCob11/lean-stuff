import Mathlib
open unitInterval

abbrev Irr2 : Set (ℝ × ℝ) := {x | Irrational x.1 ∨ Irrational x.2}
example : Irr2 = (Set.range Rat.cast ×ˢ Set.range Rat.cast)ᶜ := Set.ext fun _ ↦ not_and_or.symm

noncomputable local instance : DecidablePred Irrational := Classical.decPred Irrational in
example : IsPathConnected Irr2 :=
  let ⟨q₀, hq₀, _⟩ := exists_irrational_btwn zero_lt_one
  let x₀ := (q₀, q₀)
  let walk {x y : ℝ} : Path x y := {
    toFun t := (σ t) * x + t * y
    continuous_toFun := .add
      (.mul continuous_symm.subtype_val continuous_const)
      (.mul continuous_subtype_val continuous_const)
    source' := by simp
    target' := by simp
  }
  let p {y} : Path x₀ y := if Irrational y.1 then
    .trans (.prod walk (.refl q₀)) (.prod (.refl y.1) walk) else
    .trans (.prod (.refl q₀) walk) (.prod walk (.refl y.2))
  have hp {y} (hy: y ∈ Irr2) t : @p y t ∈ Irr2 := by
    dsimp [p]
    by_cases hy₁: Irrational y.1;
    all_goals
      simp only [Path.trans_apply, hy₁, ↓reduceIte]
      split
    exacts [.inr hq₀, .inl hy₁, .inl hq₀, .inr <| hy.resolve_left hy₁]
  .intro x₀ <| .intro (.inl hq₀) fun hy ↦ ⟨p, hp hy⟩
