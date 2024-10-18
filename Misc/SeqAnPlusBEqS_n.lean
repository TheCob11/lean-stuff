import Mathlib

def solution : (ℕ → ℤ) → Prop := (∀a b : ℤ, ∃n, · n = a * n + b)

example : Exists solution := sorry
