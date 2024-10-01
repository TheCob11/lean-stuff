import Mathlib
def ZCls := ℕ × ℕ

namespace ZCls
instance : OfNat ZCls n := ⟨(n, 0)⟩
instance : NatCast ZCls := ⟨(·, 0)⟩
instance : IntCast ZCls where intCast
  | .ofNat n => n
  | .negSucc n => (0, n + 1)

def toInt (self: ZCls) : ℤ := self.1 - self.2
theorem intCast_toInt : toInt.LeftInverse IntCast.intCast := fun n ↦ by
  dsimp only [Int.cast, IntCast.intCast, toInt]
  split <;> exact rfl

abbrev rel (a b : ZCls) : Prop := a.1 + b.2 = b.1 + a.2
def rel.iseqv : Equivalence rel where
  refl _ := rfl
  symm := Eq.symm
  trans h1 h2 := by linarith

instance : Setoid ZCls := ⟨rel, rel.iseqv⟩
instance : DecidableRel fun (a b : ZCls) ↦ a ≈ b := fun _ _ ↦ decEq _ _
instance : DecidableRel instSetoid.r := fun _ _ ↦ decEq _ _

def equivNatPair : ZCls ≃ ℕ × ℕ := .refl ZCls
instance : Encodable ZCls := .ofEquiv _ equivNatPair
end ZCls

def Z := Quotient ZCls.instSetoid

namespace Z

lemma Quotient.mk_eq_iff_rep [s : Setoid α] [DecidableRel s.r] [Encodable α]
  {x : α} {y : Quotient s} : ⟦x⟧ = y ↔ x ≈ y.rep := by
  rw [Quotient.mk_eq_iff_out]
  have : y.out ≈ y.rep := Quotient.eq_mk_iff_out.mp y.rep_spec.symm
  have mp (h : x ≈ y.out) : x ≈ y.rep := Setoid.trans h this
  have mpr (h : x ≈ y.rep) : x ≈ y.out := Setoid.trans h (Setoid.symm this)
  exact ⟨mp, mpr⟩

instance : OfNat Z n := ⟨⟦n⟧⟩
instance : NatCast Z := ⟨(⟦·⟧)⟩
instance : IntCast Z := ⟨(⟦·⟧)⟩

def equivInt : Z ≃ ℤ where
  toFun n := n.rep.toInt
  invFun n := ⟦n⟧
  left_inv n := Quotient.mk_eq_iff_rep.mpr <| by
    dsimp [HasEquiv.Equiv, Setoid.r]
    zify
    let a: ℤ := (n.rep.toInt : ZCls).1
    let b: ℤ := (n.rep.toInt : ZCls).2
    let c: ℤ := n.rep.1
    let d: ℤ := n.rep.2
    have : a - b = c - d → a + d = c + b := IsAddUnit.add_eq_add_of_sub_eq_sub
      (AddGroup.isAddUnit b) (AddGroup.isAddUnit d) a c
    exact this <| ZCls.intCast_toInt n.rep.toInt
  right_inv n := by
    let nQ : Z := ⟦n⟧
    have : nQ.rep ≈ n := Setoid.symm <| Quotient.mk_eq_iff_rep.mp rfl
    conv at this =>
      dsimp only [HasEquiv.Equiv, Setoid.r]
      tactic => zify
    let a: ℤ := nQ.rep.1
    let b: ℤ := nQ.rep.2
    let c: ℤ := (n : ZCls).1
    let d: ℤ := (n : ZCls).2
    have : a - b = c - d := IsAddUnit.sub_eq_sub_iff
      (AddGroup.isAddUnit b) (AddGroup.isAddUnit d) |>.mpr this
    dsimp only [ZCls.toInt]
    exact this ▸ ZCls.intCast_toInt n

instance : CommRing Z := equivInt.commRing
def ringEquivInt : Z ≃+* ℤ := equivInt.ringEquiv
instance : Div Z := equivInt.div
#eval @id Z
  (4 * 12 - 72) / 6
  |>.rep
end Z
