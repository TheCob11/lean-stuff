import Mathlib

variable {G S : Type*} [Group G] [Group S] (f: G →* S)

-- `MonoidHom.range`
example : Subgroup S := .ofDiv (Set.range f) ⟨f 1, ⟨1, rfl⟩⟩
  fun _ ⟨x, hx⟩ _ ⟨y, hy⟩ ↦ ⟨x * y⁻¹, hx ▸ hy ▸ f.map_inv _ ▸ f.map_mul ..⟩

-- `MonoidHom.ker`
example : Subgroup G := .ofDiv {g | f g = 1} ⟨1, f.map_one⟩ fun _ hx _ hy ↦
  f.map_mul .. |>.trans <| f.map_inv _ ▸ hx ▸ hy ▸ (inv_one.substr <| mul_one _)

example : f.ker.Normal := .mk fun x hx y ↦ by
  change f (y * x * y⁻¹) = 1
  simpa only [map_mul, map_inv, conj_eq_one_iff] using hx

-- `MonoidHom.eq_iff`
example : f x = f y ↔ y⁻¹ * x ∈ f.ker := calc
  _ ↔ f x * (f y)⁻¹ = 1 := mul_inv_eq_one.symm
  _ ↔ f x * f (y⁻¹) = 1 := f.map_inv y |>.substr Iff.rfl
  _ ↔ f (x * y⁻¹) = 1 := f.map_mul x y⁻¹ |>.substr Iff.rfl
  _ ↔ x * y⁻¹ ∈ f.ker := Iff.rfl
  _ ↔ y⁻¹ * x ∈ f.ker := Subgroup.Normal.mem_comm_iff inferInstance

-- `QuotientGroup.rangeKerLift`
example : G ⧸ f.ker →* f.range where
  toFun := Quotient.lift f.rangeRestrict fun a b h ↦
    have : f (a⁻¹ * b) = 1 := QuotientGroup.leftRel_apply.mp h
    have := f.eq_iff.mpr this |>.symm
    by simpa [MonoidHom.rangeRestrict] using this
  map_mul' := Quotient.ind₂ <| fun a b ↦
    let aKer : G ⧸ f.ker := ⟦a⟧
    have : aKer * ⟦b⟧ = ⟦a * b⟧ := rfl
    by simp only [this, Quotient.lift_mk, map_mul]
  map_one' :=
    have : (1: G ⧸ f.ker) = ⟦1⟧ := rfl
    by simp only [this, Quotient.lift_mk, map_one]

open QuotientGroup renaming rangeKerLift → rKL

noncomputable
example : G ⧸ f.ker ≃* f.range where
  toFun := rKL f
  invFun := fun ⟨_s, hs⟩ ↦ ⟦hs.choose⟧
  left_inv gKer :=
    let x := rKL f gKer
    let g := gKer.out'
    have : rKL f gKer = f g := gKer.out_eq'.symm.substr rfl
    have : f (x.prop.choose) = f g := x.prop.choose_spec.trans this
    have : f (x.prop.choose⁻¹ * g) = 1 :=
      f.map_mul _ _ ▸ f.map_inv _ ▸ this ▸ mul_left_inv _
    Quotient.mk_eq_iff_out (s := _) |>.trans
      QuotientGroup.leftRel_apply |>.mpr this
  right_inv x := Subtype.eq x.prop.choose_spec
  map_mul' := map_mul _

example (ψ : S → G) (hψ : ψ.RightInverse f) : G ⧸ f.ker ≃* f.range where
  toFun := rKL f
  invFun x := ψ x
  left_inv gKer :=
    let g := gKer.out'
    have rKL_lift : rKL f gKer = f g := gKer.out_eq'.symm.substr rfl
    have : f ((ψ (f g))⁻¹ * g) = 1 :=
      f.map_mul _ g ▸ f.map_inv _ ▸ (hψ (f g)).symm ▸ mul_left_inv (f g)
    Quotient.mk_eq_iff_out (s := _) |>.trans
      QuotientGroup.leftRel_apply |>.mpr <| rKL_lift.substr this
  right_inv x := Subtype.eq <| hψ x
  map_mul' := map_mul _
