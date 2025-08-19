import Mathlib

-- example [PseudoMetricSpace A] (s: ℕ → A) (a: A):
--   (∀ε > 0, ∃N, ∀n ≥ N, dist (s n) a < ε) ↔
--   ∀A, a ∈ A ∧ IsOpen A → ∃N, ∀n ≥ N, s n ∈ A where
--   mp h _ := fun ⟨a_mem, A_open⟩ ↦
--     have ⟨ε, ⟨ε_pos, hε⟩⟩ := Metric.isOpen_iff.mp A_open a a_mem
--     h ε ε_pos |>.imp fun _N hN n a ↦ hε (hN n a)
--   mpr h _ε ε_pos := h _ ⟨Metric.mem_ball_self ε_pos, Metric.isOpen_ball⟩

-- example [PseudoMetricSpace α] (s: ℕ → α) (a: α):
--   (∀ε > 0, ∀ᶠ n in .atTop, dist (s n) a < ε) ↔
--   ∀A, a ∈ A → IsOpen A → ∀ᶠ n in .atTop, (s n) ∈ A where
--   mp h _ a_mem A_open :=
--     have ⟨ε, ⟨ε_pos, hε⟩⟩ := Metric.isOpen_iff.mp A_open a a_mem
--     h ε ε_pos |>.mono fun _n hn ↦ hε hn
--   mpr h _ ε_pos := h _ (Metric.mem_ball_self ε_pos) Metric.isOpen_ball

-- example [TopologicalSpace α] (s: ℕ → α) (a: α): Filter.Tendsto s .atTop (nhds a) ↔
--   ∀A, a ∈ A → IsOpen A → ∀ᶠ n in .atTop, (s n) ∈ A where
--   mp h A a_mem A_open := by

--     sorry
--   mpr h := sorry

-- example : Filter.atTop.Tendsto (fun n ↦ (1 / 2 ^ n : ℝ)) (nhds 0) :=
--   Metric.tendsto_atTop'.mpr fun ε (hε: 0 < ε) ↦
--   let a (n: ℕ) : ℝ := (2 ^ n)⁻¹
--   if one_le_ε: 1 ≤ ε then by
--     let N := ⌊Real.logb 2 ε⌋₊
--     refine Exists.intro N fun n (hn: N < n) ↦ ?_
--     simp only [one_div, dist_zero_right, norm_inv, norm_pow, RCLike.norm_ofNat]
--     let NR : ℝ := N
--     let nR : ℝ := n
--     have : (2: ℝ) ^ NR ≤ 2 ^ nR :=
--       Real.monotone_rpow_of_base_ge_one one_le_two <| Nat.mono_cast hn.le
--     have : 2 ^ NR < ε := by
--       -- simp_all only [Real.rpow_natCast, N, NR, nR]
--       -- have := Real.floor_logb_natCast one_lt_two hε.le
--       -- simp only [Nat.cast_ofNat] at this
--       -- have : ⌊Real.logb 2 ε⌋
--       -- simp [NR]
--       have : (2: ℝ) ^ NR = (2 ^ N : ℤ) := Real.rpow_natCast 2 N |>.trans <|
--         @Int.cast_pow ℝ _ 2 N |>.symm
--       rw [this]
--       simp [N]
--       have :=
--         (Int.ofNat_floor_eq_floor <| Real.logb_nonneg one_lt_two one_le_ε).trans
--         <| Real.floor_logb_natCast one_lt_two hε.le
--       simp [← zpow_natCast, this]
--       -- have : (2: ℝ) ^ Int.log 2 ε = (((2) ^ (Int.log 2 ε) : ℤ): ℝ) := rfl
--       -- rw?
--       sorry
--     sorry
--   else
--     have ε_le_one : ε < 1 := lt_of_not_le one_le_ε; clear% one_le_ε
--     sorry

-- section

-- open Topology
-- example : Continuous fun p: ℝ × ℝ ↦ p.1 * p.2 := Metric.continuous_iff.mpr fun (x, y) ε ε_pos ↦ by
--   let k := x^2 ⊔ y^2 + 2
--   have k_pos : 0 < k := add_pos_of_nonneg_of_pos (sq_nonneg x |>.trans le_sup_left) two_pos
--   let δ := ε / k
--   have δ_pos : δ > 0 := div_pos ε_pos k_pos
--   refine ⟨δ, δ_pos, fun (a, b) h ↦ ?_⟩
--   let d2 := dist (a, b) (x, y)
--   if hd2_zero: 0 = d2 then sorry else
--   have d2_pos : 0 < d2 := dist_nonneg.lt_of_ne hd2_zero
--   change dist (a * b) (x * y) < ε
--   have : d2 * k < ε := lt_div_iff k_pos |>.mp h
--   have : d2 * (x^2 ⊔ y^2) + d2 * 2 < ε := left_distrib d2 _ 2 |>.symm.trans_lt this
--   have : d2 * (x^2 ⊔ y^2) < ε := lt_add_iff_pos_right _ |>.mpr
--     (mul_pos d2_pos two_pos) |>.trans this
--   have := calc
--     dist (a*b) (x*y) = dist (x*y) (a*b) := dist_comm ..
--     _ ≤ dist (x*y) (a*y) + dist (a*y) (a*b) := dist_triangle ..
--     _ = |x*y - a*y| + |a*y - a*b| := rfl
--     _ = |(x-a)*y| + |a*(y-b)| := by rw [← mul_sub, ← sub_mul]
--     _ = dist x a * |y| + |a| * dist y b := by rw [abs_mul _ y, abs_mul a _]; exact rfl

--   let δx := (ε/2) / (|y| + 1)
--   -- want δy to be something like (ε/2) / (|a| + 1)
--   -- thus δ would be the ⊔ of those = (ε/2) * (1/(|y|+1) ⊔ 1/(|a|+1))
--   -- but i alr set |x-a| < (ε/2)/(|y|+1)
--   -- ε/2 > (|y|+1)|x-a|
--   -- = |(|y|+1)(x-a)|
--   -- = |(|y|+1)x - (|y|+1)a|
--   -- = dist (|y|+1)x (|y|+1)a
--   -- ≤ dist (|y|+1)x (|y|+1)  + dist (|y|+1) (|y|+1)a

--   -- ε/2 > (|y|+1)|x-a|
--   -- ≥ (|y|+1)(|x| - |a|)
--   -- = (|y|+1)|x| - (|y|+1)|a|
--   sorry

-- end

section
open Topology Metric
variable {X Y} [TopologicalSpace X] [Inhabited X] [MetricSpace Y]
         {F} [FunLike F X Y] [BoundedContinuousMapClass F X Y]

theorem bddAbove_dist {f g : F} : BddAbove <| Set.range (fun x ↦ dist (f x) (g x)) :=
  let x₀ := default
  let ⟨cf, hcf⟩ := map_bounded f
  let f₀ := f x₀
  let ⟨cg, hcg⟩ := map_bounded g
  let g₀ := g x₀
  ⟨cf + dist f₀ g₀ + cg, fun _ ⟨x, hx⟩ ↦ hx ▸
      (dist_triangle4 (f x) f₀ g₀ (g x) |>.trans <| add_le_add_three (hcf x x₀) le_rfl (hcg x₀ x))⟩

noncomputable local instance : MetricSpace F where
  dist f g := ⨆x, dist (f x) (g x)
  dist_self f := iSup_congr (dist_self ∘' f) |>.trans ciSup_const
  dist_comm f g := iSup_congr fun x ↦ dist_comm (f x) (g x)
  dist_triangle f g h := ciSup_le fun x ↦ dist_triangle (f x) (g x) (h x) |>.trans <|
    add_le_add (le_ciSup bddAbove_dist x) (le_ciSup bddAbove_dist x)
  eq_of_dist_eq_zero h := DFunLike.ext _ _ fun x ↦ dist_le_zero.mp <| h ▸ le_ciSup bddAbove_dist x

section
variable {ι} {f: ι → F} {g: F} {p: Filter ι}
example : p.Tendsto f (𝓝 g) ↔ TendstoUniformly ((⇑) ∘ f) g p := calc
  _ ↔ ∀ε > 0, ∀ᶠi in p, dist (f i) g < ε := tendsto_nhds
  _ ↔ ∀ε > 0, ∀ᶠi in p, ∀x, dist (f i x) (g x) < ε := {
    mp h ε ε_pos := h ε ε_pos |>.mono fun i hi x ↦ le_ciSup bddAbove_dist x |>.trans_lt hi
    mpr h ε ε_pos := h (ε/2) (half_pos ε_pos) |>.mono fun i hi ↦
      ciSup_le (le_of_lt ∘' hi) |>.trans_lt <| half_lt_self ε_pos
  }
  _ ↔ ∀ε > 0, ∀ᶠi in p, ∀x, dist (g x) (f i x) < ε := by conv in _ < _ => rw [dist_comm]
  _ ↔ _ := tendstoUniformly_iff.symm

example (h: p.Tendsto f (𝓝 g)) x : p.Tendsto (f · x) (𝓝 (g x)) := tendsto_nhds.mpr fun ε ε_pos ↦
  tendsto_nhds.mp h ε ε_pos |>.mono fun _i hi ↦ le_ciSup bddAbove_dist x |>.trans_lt hi
end

namespace PointwiseVsUniformConvergence1
open unitInterval BoundedContinuousFunction

def f: ℕ → I →ᵇ I := fun n ↦ .mkOfCompact {
  toFun t := t^n
  continuous_toFun := Continuous.pow continuous_induced_dom n |>.subtype_mk _
}

theorem f_n_one {n} : (f n) 1 = 1 := one_pow n

noncomputable def flim: I → I := Function.update 0 1 1

theorem flim_one : flim 1 = 1 := Function.update_self 1 1 0
theorem flim_ne_one {t} (ht: t ≠ 1) : flim t = 0 := Function.update_of_ne ht 1 0

theorem f_pointwise_tendsto (t) : Filter.atTop.Tendsto (f · t) (𝓝 (flim t)) :=
  if ht: t = 1 then ht ▸ Metric.tendsto_nhds.mpr fun _ε ε_pos ↦ .of_forall fun _ ↦
    flim_one.substr <| f_n_one.substr <| dist_self 1 |>.trans_lt ε_pos
  else tendsto_subtype_rng.mpr <| flim_ne_one ht |>.substr <|
    tendsto_pow_atTop_nhds_zero_of_lt_one t.prop.1 <| le_one'.lt_of_ne ht

theorem tendsto_flim_one : (𝓝[≠] 1).Tendsto flim (𝓝 0) := Metric.tendsto_nhdsWithin_nhds.mpr
  fun _ε ε_pos ↦
    ⟨1, one_pos, fun _t ht _ ↦ flim_ne_one ht |>.substr <| dist_self 0 |>.trans_lt ε_pos⟩

theorem not_continuousAt_flim_one : ¬ContinuousAt flim 1 := not_continuousAt_of_tendsto
  tendsto_flim_one
  inf_le_left
  (disjoint_nhds_nhds.mpr <| flim_one.trans_ne one_ne_zero)

end PointwiseVsUniformConvergence1

end
