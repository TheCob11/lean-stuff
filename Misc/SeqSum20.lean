import Mathlib
def Seq20 := {l: List ℕ // l.sum = 20 ∧ ∀n ∈ l, 1 = n ∨ 2 = n ∨ 3 = n}
namespace Seq20
open Nat List
variable {seq: Seq20}

def ones : Σ'seq: Seq20, seq.val.length = 20 := ⟨⟨List.replicate 20 1, by decide⟩, rfl⟩
example : Σ'seq: Seq20, seq.val.length = 7 := ⟨⟨[3,3,3,3,3,3,2], by decide⟩, rfl⟩

abbrev sum_eq : seq.val.sum = 20 := seq.prop.left
abbrev elem_eq (hn: n ∈ seq.val) : 1 = n ∨ 2 = n ∨ 3 = n := seq.prop.right n hn

theorem one_le (hn: n ∈ seq.val) : 1 ≤ n := by
  rcases elem_eq hn with rfl|rfl|rfl <;> exact NeZero.one_le

abbrev pos (hn: n ∈ seq.val) : 0 < n := one_le hn

theorem le_three (hn: n ∈ seq.val) : n ≤ 3 := by
  rcases elem_eq hn with rfl|rfl|rfl <;> exact le_of_ble_eq_true rfl

theorem twenty_le_len_mul_3 : 20 ≤ seq.val.length * 3 := sum_eq.symm.trans_le <|
  seq.val.sum_le_card_nsmul 3 (@le_three seq)

-- instance : Encodable Seq20 := Subtype.encodable

theorem length_le_twenty : seq.val.length ≤ 20 :=
  sum_eq.subst <| seq.val.length_le_sum_of_one_le (@one_le seq)

theorem seven_le_length : 7 ≤ seq.val.length := by linarith [seq.twenty_le_len_mul_3]

example : {l: List (Fin n) // l.length = m} ≃ Mathlib.Vector (Fin n) m := .refl _

def equivFin3Sum : Seq20 ≃ {l: List (Fin 3) // (l.map (·.val + 1)).sum = 20} where
  toFun seq := Subtype.mk
    (seq.val.attach.map fun ⟨n, hn⟩ ↦
      ⟨n - 1, sub_one_lt_of_le (pos hn) (le_three hn)⟩)
    <| by
    simp only [map_map, Function.comp]
    conv in (_ - 1 + 1) => simp only [Nat.sub_one_add_one (pos x.prop).ne']
    exact attach_map_subtype_val seq.val |>.symm ▸ seq.prop.left
  invFun x := Subtype.mk (x.val.map (·.val + 1))
    <| by
    simp_all only [sum_map_add, mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, self_eq_add_left, reduceEqDiff]
    obtain ⟨l, hl⟩ := x
    simp only
    simp_all only [sum_map_add, true_and]
    intro a a_1
    fin_cases a <;> simp
  left_inv x := Subtype.ext <| by
    simp only [map_map, Function.comp]
    conv in (_ - 1 + 1) => simp only [Nat.sub_one_add_one (pos x.prop).ne']
    simp only [attach_map_subtype_val]
  right_inv x := Subtype.ext <| List.ext_getElem
    (by simp only [length_map, length_attach])
    fun _ _ _ ↦ by simp only [Nat.add_one_sub_one, getElem_map, getElem_attach]

example (l: List ℕ) : (l.map (· + 1)).sum = l.sum + l.length := by
  simp only [sum_map_add, map_id', map_const', sum_replicate, smul_eq_mul, mul_one]

theorem card_eq : Nat.card Seq20 = sorry :=
  sorry
