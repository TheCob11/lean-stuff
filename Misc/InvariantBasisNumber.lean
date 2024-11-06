import Mathlib

section
variable {R : Type*} [Semiring R] [InvariantBasisNumber R]
         {M : Type*} [AddCommMonoid M] [Module R M]

theorem basis_fin_n_eq (b : Basis (Fin n) R M) (b' : Basis (Fin m) R M) : n = m :=
  eq_of_fin_equiv R <| b.equivFun.symm.trans b'.equivFun

theorem basis_finite_card_eq [Finite ι] [Finite ι']
  (b : Basis ι R M) (b' : Basis ι' R M) : Nat.card ι = Nat.card ι' :=
  let n := Nat.card ι
  let m := Nat.card ι'
  have bₙ : Basis (Fin n) R M := b.reindex <| Finite.equivFin ι
  have bₘ : Basis (Fin m) R M := b'.reindex <| Finite.equivFin ι'
  eq_of_fin_equiv R <| bₙ.equivFun.symm.trans bₘ.equivFun
end
