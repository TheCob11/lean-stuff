import Mathlib

-- note that each unique Module is implicitly using the AddCommGroup inst
example [AddCommGroup M] : Unique (Module ℤ M) where
  default := .ofMinimalAxioms
    (fun n x y ↦ zsmul_add x y n)
    (fun n m x ↦ add_zsmul x n m)
    (fun n m x ↦ mul_zsmul x n m)
    (one_zsmul)
  -- idk if i like the term or tactic mode better here
  uniq a := a.ext' _ fun n x ↦ n.induction_on
    (zero_zsmul x ▸ a.zero_smul x)
    (fun m h ↦ a.add_smul m 1 x ▸ (one_smul ℤ x).symm ▸
                add_zsmul x m 1 ▸ (one_zsmul x).symm ▸ h ▸ rfl)
    -- (fun m h ↦ by simp only [a.add_smul, h, one_smul, add_zsmul, one_zsmul])
    (fun m h ↦ a.add_smul (-m) (-1) x ▸ h ▸ neg_zsmul x m ▸ neg_smul (1: ℤ) x ▸
                (one_smul ℤ x).symm ▸ sub_one_zsmul x (-m) ▸ neg_zsmul x m ▸ rfl)
    -- (fun m h ↦ by simp only [Int.sub_eq_add_neg, a.add_smul, h, neg_smul,
    --     one_smul, ↓sub_one_zsmul x (-m), neg_zsmul])
