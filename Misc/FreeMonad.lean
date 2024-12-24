import Mathlib

inductive Free (f: Type u → Type v) (α: Type u) : Type (max (u+1) v)
| pure : α → Free f α
| impure {β} : f β → (β → Free f α) → Free f α

namespace Free

protected def bind (x: Free f α) (k: α → Free f β) : Free f β := match x with
| .pure x => k x
| .impure y g => impure y fun x ↦ g x |>.bind k

instance : Monad (Free f) where
  pure := .pure
  bind := .bind

-- def out [Functor f] : Free.{0,0} f α → α ⊕ f (Free f α)
-- | pure a => .inl a
-- | impure b g => .inr <| g.comp <$> b

-- def run [Monad f] [LawfulMonad f] : Free.{max u v, v} f α → f α
-- | pure a => return a
-- | impure b g => g.comp ULift.down <$> b >>= run
-- decreasing_by {
-- · rename_i inst inst_1 β a
--   simp [InvImage, WellFoundedRelation.rel]
--   constructor
--   simp_all only [Nat.succ_eq_add_one, Nat.le_eq, nonpos_iff_eq_zero, add_eq_zero, one_ne_zero, and_false]

--   sorry
-- }

def run {m} [Monad m] [MonadLiftT f m] : Free f α → m α
| pure x => return x
| impure y g => do run <| g (← y)

inductive ListF : Type _ → Type _
| Nil : ListF PEmpty
| Cons : ListF PUnit

def myFree : Free (ListF) ℕ := do
  impure .Cons pure
  impure .Cons pure
  impure .Nil PEmpty.elim


inductive InputLayer : Type _ → Type _
| mk : (input_size: ℕ) → InputLayer PEmpty
inductive HiddenLayer : Type _ → Type _
| mk : (input_size output_size : ℕ) → HiddenLayer PUnit

def myLayers : Free (fun α ↦ InputLayer α ⊕ HiddenLayer α) α := do
  impure (.inr ⟨1, 2⟩) pure
  impure (.inr ⟨2, 4⟩) pure
  impure (.inr ⟨4, 5⟩) pure
  impure (.inr ⟨5, 3⟩) pure
  impure (.inr ⟨3, 2⟩) pure
  impure (.inl ⟨2⟩) PEmpty.elim
#reduce myLayers

-- def out [Functor f] (shrink: Free f α → μ) : Free f α → α ⊕ f μ
-- | pure a => .inl a
-- | impure b g => .inr <| shrink.comp g <$> b

-- def out' {f: Type u → Type v} {α : Type w} [Functor f] [Pure f]
--   {μ : Type u} (shrink : Free f α → μ) : Free f α → f μ
-- | pure a => Pure.pure <| shrink <| pure a
-- | impure b g => shrink.comp g <$> b

instance : LawfulMonad (Free f) where
  map_const := rfl
  id_map := Free.rec (fun _ ↦ rfl)
    fun _ _ h ↦ by simp_all [Functor.map, Free.bind]
  seqLeft_eq x y := x.recOn (fun _ ↦ rfl)
    fun _ _ ih ↦ by simpa [SeqLeft.seqLeft, Seq.seq, Free.bind] using funext ih
  seqRight_eq x y := by
    induction x
    next => exact y.recOn (fun _ ↦ rfl) <|
      fun _ _ ih => by simpa [SeqRight.seqRight, Seq.seq, Free.bind] using funext ih
    next ih => simpa [SeqRight.seqRight, Seq.seq, Free.bind] using funext ih
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc x g h := x.recOn (fun _ ↦ rfl)
    fun _ _ ih ↦ by simpa [bind, Free.bind] using funext ih

def traverse {f: Type (u+1) → Type u} [Functor f]
  {m : Type _ → Type _} [Applicative m]
  {α β : Type (u+1)}
  (g: α → m β) :
  Free f α → m (Free f β)
| pure a => .pure <$> g a
| impure (β := γ) b h =>
  let ooga: f (Free f α) := h.comp ULift.down <$> b
  let booga := (traverse g) <$> ooga
  by
  #check run <$> ooga
  sorry

instance [Functor f] : Traversable (Free f) := ⟨traverse⟩
-- instance [Functor f] : Traversable (Free f) where
--   traverse {m} _ α β g := fun
-- | pure a => .pure <$> g a
-- | impure (β := γ) b h =>
--   -- let unga := impure (h <$> b) pure
--   by
--   #check Free f
--   sorry

end Free

def FreeM (f : Type u → Type v) (α: Type u) :=
  ((m: _ → _) → [Monad m] → [MonadLiftT f m] → [LawfulMonad m] → m α)

namespace FreeM

instance : Monad (FreeM f) where
  pure x _m := pure x
  bind x g m := x m >>= (g · m)

def run [Monad m] [LawfulMonad m] (x: FreeM m α) : m α := x m

end FreeM

example {f : Type u → Type u} {α : Type u} : FreeM f α ≃ Free f α where
  toFun x := sorry
  invFun f := sorry
  left_inv := sorry
  right_inv := sorry
