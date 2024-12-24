import Mathlib

class Layer (L : Type*) (R: outParam _) where
  (inputSize outputSize : L → ℕ)
  pass (l: L) (input: Fin (inputSize l) → R): Fin (outputSize l) → R
  -- pass (l: L) (input: Fin io.1 → R): Fin io.2 → R
namespace Layer
-- abbrev inputSize  [Layer L io R] (_l: L) := io.1
-- abbrev outputSize [Layer L io R] (_l: L) := io.2

instance (α) (β: α → Type _) [∀a, Layer (β a) R] : Layer (Σa, (β a)) R where
  -- inputSize l := inputSize l.snd
  -- outputSize l := outputSize l.snd
  pass l := pass l.snd

instance [i₁ : Layer L₁ R] [i₂ : Layer L₂ R] : Layer (L₁ ⊕ L₂) R where
  inputSize := Sum.elim i₁.inputSize i₂.inputSize
  outputSize := Sum.elim i₁.outputSize i₂.outputSize
  pass := Sum.rec i₁.pass i₂.pass

end Layer

structure LinearLayer (R) where
  {inputSize outputSize : ℕ}
  weights : Matrix (Fin outputSize) (Fin inputSize) R
  biases : Fin outputSize → R
deriving Repr

instance : Functor (LinearLayer) where
  map f l := {
    weights := l.weights.map f
    biases := f ∘ l.biases
  }

-- instance : Applicative (LinearLayer) where
--   map f l := {
--     weights := l.weights.map f
--     biases := f ∘ l.biases
--   }
--   pure a := {
--     weights := .of fun _ _ ↦ a
--     biases := fun _ ↦ a
--   }
--   seq l f := {
--     weights := .of fun i j ↦ l.weights i j <| f () |>.weights i j
--     biases := fun i ↦ l.biases i <| f () |>.biases i
--   }

open Matrix in
instance [Mul R] [Add R] [Zero R] :
  Layer (LinearLayer R) R where
  -- inputSize := LinearLayer.inputSize
  -- outputSize := LinearLayer.outputSize
  pass l x := (l.weights.mulVecᵣ x) + l.biases

-- structure ActivationLayer (inputSize outputSize : ℕ) (R : Type _) where
--   name : String
--   toFun : (Fin inputSize → R) → (Fin outputSize → R)

-- instance : Repr (ActivationLayer _i _o _R) where
--   reprPrec x := reprPrec x.name

-- instance : Layer (ActivationLayer i o R) R where
--   inputSize := i
--   outputSize := o
--   pass := ActivationLayer.toFun

structure Network.Size where
  input : ℕ
  hiddens: List ℕ
  output : ℕ
deriving Repr

def Network.Size.cons (n: ℕ): Network.Size → Network.Size
| ⟨i, hs, o⟩ => ⟨n, i :: hs, o⟩

inductive Network (R L : Type*)
| out (l: L) : Network R L
| cons (l: L) : Network R L → Network R L

namespace Network
open Layer
infixr:67 " ::ₙ " => Network.cons

def size [Layer L R] : Network R L → Size
| .out l => ⟨inputSize l, [], outputSize l⟩
| .cons l net => Size.cons (inputSize l) <| size net

def map {α β} (f: α → β) : Network R α → Network R β
| out l => out <| f l
| l ::ₙ net => f l ::ₙ map f net

instance : Functor (Network R) where
  map := map

def traverse [Applicative m] (f: α → m β) : Network R α → m (Network R β)
| out l => out <$> f l
| l ::ₙ net => cons <$> f l <*> traverse f net

instance : Traversable (Network R) := ⟨traverse⟩

instance : Pure (Network R) := ⟨out⟩

instance [Repr L] : Repr (Network R L) where
  reprPrec := reprPrec ∘ Traversable.toList

def inputLayer : Network R L → L
| out l | l ::ₙ _ => l

def hiddenLayers : Network R L → List L
| out _i | _i ::ₙ out _o => []
| _ ::ₙ h ::ₙ hs => h :: hs.hiddenLayers

def outputLayer : Network R L → L
| out l => l
| _ ::ₙ net => net.outputLayer

def toInputProdRest : Network R L → L × List L
| out l => (l, [])
| l ::ₙ net => (l, Traversable.toList net)

def ofInputProdRest : L × List L → Network R L
| (l, []) => out l
| (l, h :: hs) => l ::ₙ ofInputRest h hs

def equivInputRest : Network R L ≃ L × List L where
  toFun := toInputProdRest
  invFun := ofInputRest.uncurry
  left_inv := rec (fun _ ↦ rfl)
    fun _ _ ih ↦ by unfold ofInputRest;

end Network

def myNet : Network ℚ (LinearLayer ℚ) :=
  let l_i := {
    weights := !![0.1; 0.2]
    biases := 0
  }
  let l_h := {
    weights := !![0.1, 0.5; 0.2, 0.4; 0.3, 0.3]
    biases := 0
  }
  let l_out := {
    weights := !![0.1, 0.2, 0.3]
    biases := 0
  }
  l_i ::ₙ l_h ::ₙ .out l_out

#eval myNet

example [Ring R]
  (w₁ : Matrix  (Fin 3) (Fin 2) R) (b₁ : Fin 3 → R)
  (w₂ : Matrix  (Fin 5) (Fin 3) R) (b₂ : Fin 5 → R)
  (w₃ : Matrix  (Fin 4) (Fin 5) R) (b₃ : Fin 4 → R)
  (w₄ : Matrix  (Fin 3) (Fin 4) R) (b₄ : Fin 3 → R) :
  Network R (LinearLayer R) :=
  ⟨w₁, b₁⟩ ::ₙ
    ⟨w₂, b₂⟩ ::ₙ
      ⟨w₃, b₃⟩ ::ₙ
        .out ⟨w₄, b₄⟩

-- https://prng.di.unimi.it/
def Float.random [RandomGen g] [Monad m] : RandGT g m Float := do
  let n : UInt64 := ⟨← Random.randFin⟩
  return (n >>> 11).toFloat.mul <| .scaleB 1 (-53)

instance [Monad m] : Random m Float where
  random := Float.random

instance randomOfDenumerable [Monad m] [inst: Denumerable α] : Random m α where
  random := inst.ofNat <$> Rand.next
-- #eval IO.runRandWith 15 <| @Random.rand Id StdGen ℚ _ _
