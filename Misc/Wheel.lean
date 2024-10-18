import Mathlib


class Wheel (α) extends AddCommMonoid α, DivisionCommMonoid α, Bot α, Top α where
  bot_eq : (⊥: α) = 0 * 0⁻¹
  top_eq : (⊤: α) = 1 * 0⁻¹
  right_distrib' (a b c : α) : (a + b) * c + 0 * c = a * c + b * c
  -- mul_inv_right_distrib' (a b c : α) : (a + b * c) * b⁻¹ = a * b⁻¹ + c + 0 * c

namespace Wheel
variable {α} [inst: Wheel α] (a b c : α)

local prefix:75 "/" => Inv.inv
example : a / b = a * /b := div_eq_mul_inv a b

theorem inv_mul : /(a * b) = /a * /b :=
  mul_inv_rev _ _ |>.trans <| mul_comm _ _

theorem zero_mul_inv_zero : 0 * /0  = (⊥: α) := bot_eq.symm

theorem zero_div_zero : 0 / 0 = (⊥: α) := zero_mul_inv_zero.subst <| div_eq_mul_inv 0 0

example : (a + b * c) * b⁻¹ = a * b⁻¹ + c + 0 * b := by

  sorry
end Wheel
