import Mathlib

def Solution (f: ℕ → ℤ) : Prop := ∀a b : ℤ, ∃n, f n = a * n + b

namespace Solution

def pair : ℕ ≃ (ℤ × ℤ) := Denumerable.eqv _ |>.symm

def f (n: ℕ) : ℤ :=
  let (a, b) := pair n
  a * n + b

theorem f_sol : Solution f := fun a b ↦ .intro (pair.symm (a, b)) <|
  by simp only [f, pair, Equiv.toFun_as_coe,
                Equiv.symm_symm, Equiv.symm_apply_apply]
