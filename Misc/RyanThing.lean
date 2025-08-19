import Mathlib

open Topology
variable {X Y} [TopologicalSpace X] [TopologicalSpace Y]

def equivAt (x: X) : Rel C(X, Y) C(X, Y) := fun f g ↦ ∃U, IsOpen U ∧ x ∈ U ∧ U.EqOn f g
namespace equivAt
theorem Equivalence {x : X} : Equivalence (equivAt (Y := Y) x) where
  refl _ := ⟨Set.univ, isOpen_univ, trivial, fun _ _ ↦ rfl⟩
  symm | ⟨U, hU, x_mem, h⟩ => ⟨U, hU, x_mem, h.symm⟩
  trans
  | ⟨U, U_open, x_mem_U, hU⟩, ⟨V, V_open, x_mem_V, hV⟩ =>
    ⟨U ∩ V, U_open.inter V_open, ⟨x_mem_U, x_mem_V⟩,
      fun _y ⟨y_mem_U, y_mem_V⟩ ↦ hU y_mem_U |>.trans <| hV y_mem_V⟩

theorem eq_at_x {x: X} (h: equivAt x (Y := Y) f g) : f x = g x :=
  let ⟨_, _, x_mem, hU⟩ := h
  hU x_mem

instance setoid (x: X) : Setoid C(X, Y) where
  r := equivAt x
  iseqv := equivAt.Equivalence

theorem mul [Mul Y] [ContinuousMul Y] {x : X} {a b c d : C(X, Y)} :
  equivAt x a b → equivAt x c d → equivAt x (a * c) (b * d) :=
  fun ⟨U, U_open, x_mem_U, hU⟩ ⟨V, V_open, x_mem_V, hV⟩ ↦
    ⟨U ∩ V, U_open.inter V_open, ⟨x_mem_U, x_mem_V⟩,
      fun _y ⟨hyU, hyV⟩ ↦ by simp [ContinuousMap.mul_apply, hU hyU, hV hyV]⟩

theorem add [Add Y] [ContinuousAdd Y] {x: X} {a b c d : C(X, Y)} :
  equivAt x a b → equivAt x c d → equivAt x (a + c) (b + d) :=
  fun ⟨U, U_open, x_mem_U, hU⟩ ⟨V, V_open, x_mem_V, hV⟩ ↦
    ⟨U ∩ V, U_open.inter V_open, ⟨x_mem_U, x_mem_V⟩,
      fun y ⟨hyU, hyV⟩ ↦ by simp only [ContinuousMap.add_apply, hU hyU, hV hyV]⟩

section YRing
variable [Ring Y] [TopologicalRing Y]

instance ringCon (x: X) : RingCon C(X, Y) :=
  {equivAt.setoid x with
    mul' := equivAt.mul
    add' := equivAt.add}
def C (x: X) := Quotient (setoid x (Y := Y))
instance {x: X} : Ring (C x (Y := Y)) :=
  ringCon x (Y := Y) |>.instRingQuotient

example {x: X} (q: C x (Y := Y)) (h: q = 0) : equivAt x q.out' 0 :=
  h.substr <| @Quotient.mk_out _ (setoid x) 0

def φ {x: X} : (C x (Y := Y)) →+* Y where
  toFun := Quotient.lift (· x) fun _ _ h ↦ h.eq_at_x
  map_one' := rfl
  map_mul' := Quotient.ind₂ fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := Quotient.ind₂ fun _ _ ↦ rfl

instance {x: X} : RingHomSurjective (φ (x := x) (Y := Y)) :=
  ⟨fun y ↦ ⟨⟦.const X y⟧, rfl⟩⟩

abbrev ℳ (x: X) : Ideal (C x (Y := Y)) := RingHom.ker φ
end YRing

section YField
variable [Field Y] [TopologicalRing Y]
instance {x: X} : CommRing (C x (Y := Y)) := ringCon x (Y := Y).instCommRingQuotient

namespace ℳ
theorem mk_mem_iff (f: C(X, Y)) {x: X} : ⟦f⟧ ∈ ℳ x ↔ f x = 0 := Iff.rfl
theorem not_one_mem {x: X} : 1 ∉ ℳ x (Y := Y) := fun h: (1: C(X, Y)) x = 0 ↦
  one_ne_zero <| h.subst <| ContinuousMap.one_apply x
-- noncomputable
-- def quotEquivRange {x: X} : C x (Y := Y) ⧸ ℳ x ≃+* φ (x := x) (Y := Y).range :=
--   φ.quotientKerEquivRange

-- noncomputable
-- def quotEquivTop {x: X} : C x (Y := Y) ⧸ ℳ x ≃+* (⊤: Subring Y) :=
--   φ (x := x) (Y := Y).range_top_of_surjective φ.surjective ▸ φ.quotientKerEquivRange

-- noncomputable
-- def quotEquivY {x: X} : C x (Y := Y) ⧸ ℳ x ≃+* Y := quotEquivTop.trans NonUnitalSubsemiring.topEquiv

noncomputable
def quotientEquiv (x: X) : C x (Y := Y) ⧸ ℳ x (Y := Y) ≃+* Y :=
  RingHom.quotientKerEquivOfSurjective <| φ (x := x) (Y := Y).surjective

noncomputable
instance {x: X} : Field (C x (Y := Y) ⧸ ℳ x (Y := Y)) := quotientEquiv x (Y := Y).field

noncomputable
instance {x: X} : (ℳ x (Y := Y)).IsMaximal :=
  -- typeclass inference w/`Field.toIsField` is being wonky
  Ideal.Quotient.maximal_of_isField _ <|
    @IsField.mk _ (_) Nontrivial.exists_pair_ne mul_comm
      fun {a} ha ↦ ⟨a⁻¹, sorry⟩

end ℳ
end YField
