import Mathlib
open FirstOrder

section DecidableRealize
variable {L: Language} {M} [L.Structure M]

namespace FirstOrder.Language
namespace BoundedFormula

variable {α} {l: ℕ} {ϕ ψ : L.BoundedFormula α l}
         {v: α → M} {xs: Fin l → M}
         {t₁ t₂ : L.Term (α ⊕ Fin l)}

variable (ϕ) (v) (xs)
abbrev DecidableRealize := Decidable (ϕ.Realize v xs)
variable {ϕ} {v} {xs}
variable [DecidableRealize ϕ v xs] [DecidableRealize ψ v xs]

instance : @DecidableRealize L M _ α l ⊥ v xs := instDecidableFalse

instance : DecidableRealize ϕ.not v xs := instDecidableNot
instance : @DecidableRealize L M _ α l ⊤ v xs := instDecidableNot

instance [DecidableEq M] : DecidableRealize (.equal t₁ t₂) v xs :=
  decidable_of_iff' _ <| realize_bdEqual t₁ t₂
instance [DecidableEq M] : DecidableRealize (t₁ =' t₂) v xs := instDecidableRealizeEqualOfDecidableEq

instance : DecidableRealize (ϕ ⊓ ψ) v xs := decidable_of_iff' _ <| realize_inf
instance : DecidableRealize (ϕ ⊔ ψ) v xs := decidable_of_iff' _ <| realize_sup
instance : DecidableRealize (ϕ.imp ψ) v xs := decidable_of_iff' _ <| realize_imp
instance : DecidableRealize (ϕ.iff ψ) v xs := decidable_of_iff' _ <| realize_iff

instance [Decidable <| ∀a, @Realize L M _ α (l + 1) θ v (Fin.snoc xs a)] :
  DecidableRealize (∀' θ) v xs := decidable_of_iff' _ <| realize_all
instance [Decidable <| ∃a, @Realize L M _ α (l + 1) θ v (Fin.snoc xs a)] :
  DecidableRealize (∃' θ) v xs := decidable_of_iff' _ <| realize_ex

end BoundedFormula

abbrev DecidableFormula (ϕ: L.Formula α) (v: α → M) := Decidable (ϕ.Realize v)
instance {ϕ : L.Formula α} {v: α → M}
  [inst: ϕ.DecidableRealize v default] : DecidableFormula ϕ v := inst

instance {ϕ : L.Sentence} [inst: DecidableFormula ϕ (default: _ → M)] : Decidable (M ⊨ ϕ) := inst
end FirstOrder.Language

end DecidableRealize

open Language Ring
/-
# The Freshman's Dream
`∀a b, (a + b) * (a + b) = (a * a) + (b * b)`
i rewrote this definition a bunch but some of the iterations felt like they were worth leaving here
-/
-- def freshmansDream : ring.Sentence := .all <| .all <| .equal
--   (func .mul ![func .add ![var (.inr 0), var (.inr 1)], func .add ![var (.inr 0), var (.inr 1)] ])
--   (func .add ![func .mul ![var (.inr 0), var (.inr 0)], func .mul ![var (.inr 1), var (.inr 1)] ])

-- it's pretty cold, good thing this expression is bundled up in parenthesis
-- def freshmansDream : ring.Sentence :=
--   ∀' ∀' (((var (.inr 0) + var (.inr 1)) * (var (.inr 0) + var (.inr 1))) ='
--          ((var (.inr 0) * var (.inr 0)) + (var (.inr 1) * var (.inr 1))))

-- this feels like bad practice but im really sick of the .inr-ing
local instance [inst: OfNat (Fin m) n] : OfNat (Empty ⊕ (Fin m)) n := ⟨.inr inst.ofNat⟩ in
def freshmansDream : ring.Sentence := .alls (n := 2) <|
  ((var 0 + var 1) * (var 0 + var 1)) =' ((var 0 * var 0) + (var 1 * var 1))

instance : CompatibleRing ℤ := compatibleRingOfRing _
local instance : ring.Structure Unit := Inhabited.trivialStructure ring

#eval @Term.realize ring ℤ _ Empty default <| 1 + 1

#eval @Term.realize ring ℤ _ _ ![3, 10] <| (var 0 + var 1) * (var 0 + var 1)

#eval @Term.realize ring ℤ _ _ ![3, 10] <| (var 0 * var 0) + (var 1 * var 1)

#eval
  let s : ring.Sentence := 1 =' (1 + 1)
  ℤ ⊨ s

example : ¬ℤ ⊨ freshmansDream := fun h ↦ absurd (h 1 1) <| by decide
example : Unit ⊨ freshmansDream := fun () ↦ by decide
