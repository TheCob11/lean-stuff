import Mathlib

variable {X}

class IsNearness (r: Rel X (Set X)) : Prop where
  near_empty {x} : ¬r x ∅
  near_mem {x A} : x ∈ A → r x A
  near_union {x A B} : r x (A ∪ B) → r x A ∨ r x B
  near_trans {x A B} (hA: ∀a ∈ A, r a B) (hx: r x A) : r x B

variable {r: Rel X (Set X)} [IsNearness r]

namespace IsNearness

theorem near_subset {x A B} (h: A ⊆ B) : r x A → r x B := near_trans fun _ ha ↦ near_mem (h ha)

end IsNearness

open IsNearness Topology
namespace TopologicalSpace

theorem isClosed_ofClosed : IsClosed[ofClosed T h₁ h₂ h₃] A ↔ A ∈ T :=
  @isOpen_compl_iff ..|>.symm.trans <| .of_eq <| congrArg _ <| compl_compl A

variable (r)
def ofNearness : TopologicalSpace X := .ofClosed
  {A | ∀{x}, r x A → x ∈ A}
  near_empty
  (fun _ hA _ hx _ ha ↦ hA ha <| near_subset (Set.sInter_subset_of_mem ha) hx)
  fun _ hA _ hB _ hx ↦ near_union hx |>.imp hA hB
variable {r} {A: Set X}

theorem isClosed_ofNearness : IsClosed[ofNearness r] A ↔ ∀{x}, r x A → x ∈ A := isClosed_ofClosed

theorem closure_ofNearness (A) : closure[ofNearness r] A = {x | r x A} := eq_of_le_of_le
  (@closure_minimal _ _ _ (_) (fun _ ↦ near_mem) (isClosed_ofNearness.mpr (near_trans fun _ ↦ id)))
  fun _ ↦ isClosed_ofNearness.mp (@isClosed_closure ..) ∘ near_subset (@subset_closure _ _ (_))
