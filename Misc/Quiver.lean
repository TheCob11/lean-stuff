import Mathlib
open CategoryTheory
namespace Quiver

section IsSource
class IsSource [Quiver V] (v : V) : Prop where
  empty (u) : IsEmpty (u ⟶ v)

theorem IsSource.elim [Quiver V] [inst: IsSource v] (u: V) : ¬(u ⟶ v) := inst.empty u |>.elim

instance [Quiver V] {v: V} [inst: IsSource v] : IsEmpty (Costar v) where
  false | ⟨u, f⟩ => inst.empty u |>.elim f

instance [Quiver V] {v: V} [inst: IsEmpty (Costar v)] : IsSource v where
  empty u := ⟨fun f ↦ inst.false ⟨u, f⟩⟩

theorem isSource_iff_isEmpty_costar [Quiver V] (v: V) : IsSource v ↔ IsEmpty (Costar v) where
  mp _ := inferInstance
  mpr _ := inferInstance

end IsSource

section IsTarget
class IsTarget [Quiver V] (v: V) : Prop where
  empty (u) : IsEmpty (v ⟶ u)

theorem IsTarget.elim [Quiver V] [inst: IsTarget v] (u: V) : ¬(v ⟶ u) := inst.empty u |>.elim

instance [Quiver V] {v: V} [inst: IsTarget v] : IsEmpty (Star v) where
  false | ⟨u, f⟩ => inst.empty u |>.elim f

instance [Quiver V] {v: V} [inst: IsEmpty (Star v)] : IsTarget v where
  empty u := ⟨fun f ↦ inst.false ⟨u, f⟩⟩

theorem isTarget_iff_isEmpty_costar [Quiver V] (v: V) : IsTarget v ↔ IsEmpty (Star v) where
  mp _ := inferInstance
  mpr _ := inferInstance

end IsTarget

abbrev Representation [Q: Quiver V] (R) [Ring R] :=
  Cat.free.obj ⟨V, Q⟩ ⥤ ModuleCat R

namespace Representation

instance [Q: Quiver V] [Ring R] : Coe (V ⥤q ModuleCat R) (Q.Representation R) :=
  ⟨Quiv.lift⟩

instance [Q: Quiver V] [Ring R] : Coe (Q.Representation R) (V ⥤q ModuleCat R) where
  coe W := ⟨W.obj, W.map ∘ Hom.toPath⟩

abbrev mk [Q: Quiver V] [Ring R] (obj: V → ModuleCat R) (map: {a b : V} → (a ⟶ b) → (obj a ⟶ obj b)) :
  Q.Representation R := @Quiv.lift V Q _ _ ⟨obj, map⟩

-- abbrev Quiver.Representation [Quiver V] (R) [Ring R] :=
--   V ⥤q ModuleCat R

-- abbrev Quiver.Representation.mk {Q: Quiver V} [Ring R] : (obj: V → ModuleCat R) →
--   (map: {a b : V} → (a ⟶ b) → (obj a ⟶ obj b)) → Q.Representation R := .mk

namespace Example1
-- inductive V
-- | A | B | C | D

-- def Q : Quiver (Fin 4) where
--   Hom
--   | 0, 1
--   | 1, 1
--   | 1, 2
--   | 1, 3 => Unit
--   | _, _ => Empty

def V := Fin 4

instance : OfNat V n := Fin.instOfNat

inductive E: V → V → Type _
| a : E 0 1
| b : E 1 1
| c : E 1 2
| d : E 1 3

instance Q: Quiver V := ⟨E⟩

-- def Q : Quiver V where
--   Hom
--   | .A, .B
--   | .B, .B
--   | .B, .C
--   | .B, .D => Unit
--   | _, _ => Empty

def W : Q.Representation ℚ := .mk
  ![⟨Fin 3 → ℚ⟩, ⟨Fin 2 → ℚ⟩, ⟨ℚ⟩, ⟨Fin 4 → ℚ⟩]
  fun
  | E.a => Matrix.mulVecLin !![1, 2, 3; 2, 3, 4]
  | E.b => Matrix.mulVecLin !![1, 2; 3, 4]
  | E.c => LinearEquiv.funUnique ..|>.comp <| Matrix.mulVecLin !![1,3]
  | E.d => Matrix.mulVecLin !![1, 2; 2, 3; 3, 4; 4, 5]

#eval W.map (.toPath E.b) ![1, 3]

def U : Q.Representation ℚ := .mk
  ![⟨Fin 4 → ℚ⟩, ⟨Fin 5 → ℚ⟩, ⟨Fin 3 → ℚ⟩, ⟨Fin 2 → ℚ⟩]
  fun
  | E.a => 0
  | E.b => 0
  | E.c => 0
  | E.d => 0

-- commenting this out bc the automatic `aesop_cat` for `naturality` is a lil slow
-- example : W ⟶ U where
--   app
--   | ⟨0, _⟩ => 0
--   | ⟨1, _⟩ => 0
--   | ⟨2, _⟩ => 0
--   | ⟨3, _⟩ => 0

end Example1

variable {V R} [Q: Quiver V] [Ring R]

/-
definition of morphism of representations as presented in the paper, comes
free with category setup :)
-/
example (W U : Q.Representation R) (τ : ∀v, W.obj v →ₗ[R] U.obj v)
  (h: ∀a b (e: a ⟶ b), (τ b).comp (W.map e) = (U.map e).comp (τ a)) : W ⟶ U :=
  ⟨τ, h⟩

abbrev IsThin (W: Q.Representation R) := ∀v, Module.rank R (W.obj v) ≤ 1

end Representation

section Net

variable {V} [Q: Quiver V] (layer: Type*) (ι: layer → Type*) [PartialOrder layer]

@[ext]
structure Layers extends Equiv (Sigma ι) V where
  -- layers : (l: layer) → (ι l) → V
  -- layers_forward : ∀(l₁ l₂) (i₁) (i₂), ((layers l₁ i₁) ⟶ (layers l₂ i₂)) → l₁ ≤ l₂
  -- layers_endo : ∀l (i₁ i₂), ((layers l i₁) ⟶ (layers l i₂)) → i₁ = i₂ ∨ IsSource (layers l i₁)
  -- nodes : Sigma ι ≃ V
  layers_forward : (u ⟶ v) → (invFun u).fst ≤ (invFun v).fst
  layer_endo : (u ⟶ v) → (invFun u).fst = (invFun v).fst → u = v ∨ IsSource u

variable {layer} {ι}

instance : EquivLike (Q.Layers layer ι) (Sigma ι) V where
  coe x := x.toFun
  inv x := x.invFun
  left_inv x := x.left_inv
  right_inv x := x.right_inv
  coe_injective' x _ := x.ext

example [Q: Quiver V] [PartialOrder layer] (L: Q.Layers layer ι) {u v : V} (f: u ⟶ v) :
  (u = v ∨ IsSource u) ∨ (L.symm u).fst < (L.symm v).fst :=
  L.layers_forward f |>.eq_or_lt.imp_left <| L.layer_endo f

class IsNetwork [Q: Quiver V] where
  loop_subsingleton {v: V} : Subsingleton (v ⟶ v)
  loop_source {v} : (v ⟶ v) → ¬Q.IsSource v ∧ ¬Q.IsTarget v

end Net
