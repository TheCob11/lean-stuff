import Mathlib
def Seq20 := {l: List ℕ // l.sum = 20 ∧ ∀n ∈ l, 1 = n ∨ 2 = n ∨ 3 = n}
namespace Seq20
open Nat List
variable {seq: Seq20}

def ones : Σ'seq: Seq20, seq.val.length = 20 := ⟨⟨List.replicate 20 1, by decide⟩, rfl⟩
example : Σ'seq: Seq20, seq.val.length = 7 := ⟨⟨[3,3,3,3,3,3,2], by decide⟩, rfl⟩

abbrev sum_eq : seq.val.sum = 20 := seq.prop.left
abbrev elem_eq (hn: n ∈ seq.val) : 1 = n ∨ 2 = n ∨ 3 = n := seq.prop.right n hn

theorem one_le : ∀n ∈ seq.val, 1 ≤ n := fun _ hn ↦ by
  rcases elem_eq hn with rfl|rfl|rfl <;> exact NeZero.one_le

abbrev pos : ∀n ∈ seq.val, 0 < n := one_le

theorem le_three : ∀n ∈ seq.val, n ≤ 3 := fun _ hn ↦ by
  rcases elem_eq hn with rfl|rfl|rfl <;> exact le_of_ble_eq_true rfl

theorem twenty_le_len_mul_3 : 20 ≤ seq.val.length * 3 := sum_eq.symm.trans_le <|
  seq.val.sum_le_card_nsmul 3 le_three

instance : Encodable Seq20 := Subtype.encodable

theorem length_le_twenty : seq.val.length ≤ 20 :=
  sum_eq.subst <| seq.val.length_le_sum_of_one_le one_le

theorem seven_le_length : 7 ≤ seq.val.length := by linarith [seq.twenty_le_len_mul_3]

example : Nat.card (Fin 7 → Fin 3) = 3 ^ 7 := by simp only [card_eq_fintype_card, Fintype.card_pi,
  Fintype.card_fin, Finset.prod_const, Finset.card_univ, reducePow]

example : {l: List (Fin n) // l.length = m} ≃ Mathlib.Vector (Fin n) m := .refl _

example : Seq20 ↪ List ℕ := .subtype _
example : Seq20 ≃ {l: List (Fin 4) // (l.map Fin.val).sum = 20 ∧ ∀n ∈ l, 0 < n} where
  toFun seq := ⟨seq.val.map fun n ↦ ⟨n, sorry⟩, sorry⟩
  invFun fseq := sorry
  left_inv := sorry
  right_inv := sorry

proof_wanted card_eq : Nat.card Seq20 = sorry
