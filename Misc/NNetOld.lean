import Mathlib

namespace NNet

structure Activation (R: Type*) where
  toFun : R → R
  name : String

instance : ToString (Activation R) where
  toString a := a.name

instance : Repr (Activation R) where
  reprPrec a _ := "Activation " ++ .paren a.name

structure Layer (R: Type*) where
  size: ℕ -- output size
  activation : Activation R
deriving Repr

structure Arch (R) where
  input_size: ℕ
  layers: List (Layer R)
  nonempty: 0 < layers.length := by decide
deriving Repr

namespace Arch
variable (a: Arch R)

abbrev output_size : ℕ :=
  Layer.size <| a.layers.getLast <| List.ne_nil_of_length_pos a.nonempty

abbrev layer_input_size : Fin (a.layers.length + 1) → ℕ
| 0 => a.input_size
| ⟨i + 1, _⟩ => a.layers[i].size

abbrev Weights := (l: Fin a.layers.length) →
    Matrix (Fin a.layers[l].size) (Fin (a.layer_input_size l)) R

abbrev Biases := (l: Fin a.layers.length) → Fin (a.layers[l].size) → R

end Arch

structure Network [Zero R] (arch: Arch R) where
  weights : arch.Weights
  biases : arch.Biases

-- instance [Repr R] : Repr (Matrix (Fin n) (Fin m) R) := inferInstance
def piToDFinsupp [Fintype α] [DecidableEq α] (f: (a: α) → β a) [∀a, Zero (β a)] :
  DFinsupp β := .mk .univ (fun a ↦ f a)

unsafe instance [Zero R] [Repr R] {arch: Arch R} : Repr arch.Weights where
  reprPrec x := reprPrec <| piToDFinsupp x

unsafe instance [Zero R] [Repr R] {arch: Arch R} : Repr arch.Biases where
  reprPrec x := reprPrec <| piToDFinsupp x

-- deriving instance Repr for Network
def Fin.valFinsupp [NeZero n] : Fin n →₀ ℕ where
  toFun := Fin.val
  support := .Ioi 0
  mem_support_toFun i := Finset.mem_Ioi.trans <| Iff.intro
    (fun h h₁ ↦ h.ne' <| Fin.eq_of_val_eq h₁)
    (fun h ↦ Fin.pos_iff_ne_zero' i |>.mpr <| Fin.ne_of_val_ne h)

#check Multiset.toDFinsupp
#check DFinsupp.instRepr
#eval
  let n := 5
  let x : DFinsupp (fun i: Fin n ↦ Fin (i + 1) → ℕ) := fun₀
  | 0 => ![0]
  | 1 => ![0, 1]
  | 2 => ![0, 1, 2]
  | 3 => ![0, 1, 2, 3]
  | 4 => ![0, 1, 2, 3, 4]
  x
#eval
  let x: (i: Fin 2) → Matrix (Fin i) (Fin 2) ℕ
  | 0 => !![,,]
  | 1 => !![1,2]
  piToDFinsupp x

end NNet
open NNet

-- structure ReLU {α: Type*} where
-- instance : Unique (@ReLU α) where
--   default := .mk
--   uniq _ := rfl
-- instance [Max α] [Zero α] : FunLike (@ReLU α) α α where
--   coe _ := max 0
--   coe_injective' _ _ _ := rfl
def ReLU [Max α] [Zero α] : Activation α where
  toFun := max 0
  name := "ReLU"

def floatSigmoid : Activation Float where
  toFun x := 1 / (x.neg.exp + 1)
  name := "sigmoid"

def my_arch : Arch Float where
  input_size := 2
  layers := [⟨3, ReLU⟩, ⟨1, floatSigmoid⟩]

-- https://prng.di.unimi.it/
def Float.random [RandomGen g] [Monad m] : RandGT g m Float := do
  let n : UInt64 := ⟨← Random.randFin⟩
  return (n >>> 11).toFloat.mul <| .scaleB 1 (-53)

instance [Monad m] : Random m Float where
  random := Float.random

def my_net : Network my_arch where
  biases l i := @Random.rand Id _ _ |>.eval <| pure <| mkStdGen <| l + 15*i
  weights l := .of fun i j ↦ @Random.rand Id _ _ |>.eval <| pure <| mkStdGen <|
    17 * l + 31 * i + 71 * j

-- #eval @id (Matrix (Fin (my_arch.num_layers)) (Fin 3) ℕ) <| .of fun _ _ ↦ 1
#eval my_arch
