import Mathlib

namespace Chopsticks

inductive Side | L | R deriving Repr
open Side

structure Fingers (nF: ℕ) where
  (l r: ZMod nF)
  -- for eliminating redundancies
  (l_le_r : l.val ≤ r.val := by decide)
deriving Repr, DecidableEq

namespace Fingers
abbrev get (f: Fingers nF) : Side → ZMod nF
| L => f.l | R => f.r

abbrev total (f: Fingers nF) : ℕ :=
  f.l.val + f.r.val

theorem total_le [NeZero nF] (f: Fingers nF) : f.total ≤ 2 * nF :=
  nF.two_mul ▸ Nat.add_le_add f.l.val_le f.r.val_le

abbrev mk_le (l r : ZMod nF) (h: l.val ≤ r.val) : Fingers nF := mk l r h

abbrev mk_order (n₁ n₂ : ZMod nF) : Fingers nF :=
  Nat.le_or_le n₁.val n₂.val |>.by_cases (mk_le n₁ n₂) (mk_le n₂ n₁)

def recieve (f: Fingers nF) (n: ZMod nF) (s: Side) : Fingers nF :=
  mk_order.uncurry <| match s with
  | L => (f.l + n, f.r)
  | R => (f.l,     f.r + n)
end Fingers

abbrev Player nP := Fin nP

def Game (nP nF : ℕ) := Player nP → Fingers nF
instance : Repr (Game nP nF) := PiFin.hasRepr

instance : Inhabited (Game nP nF) where
  default _ := ⟨1, 1, le_refl _⟩

structure Attack (nP) where
  (s_from s_to : Side)
  (target : Player nP)

abbrev Distrib (nF) := Fingers nF

inductive Move (nP nF)
| attack (a: Attack nP)
| distrib (d: Distrib nF)

namespace Game

variable (g: Game nP nF) (p: Player nP)
section Move

section Attack
structure attack_valid (a: Attack nP) : Prop where
  target_ne : a.target ≠ p
  from_nz : (g p).get a.s_from ≠ 0
  to_nz : (g a.target).get a.s_to ≠ 0

theorem attack_valid_iff (a: Attack nP) : g.attack_valid p a ↔
  a.target ≠ p ∧ (g p).get a.s_from ≠ 0 ∧ (g a.target).get a.s_to ≠ 0 := {
    mp  := fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩
    mpr := fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩
  }

instance : DecidablePred (g.attack_valid p) :=
  fun a ↦ decidable_of_iff' _ (g.attack_valid_iff p a)

def runAttack (a: Attack nP) (_: g.attack_valid p a) : Game nP nF :=
  Function.update g a.target <| (g a.target).recieve ((g p).get a.s_from) a.s_to

end Attack
section Distrib
structure distrib_valid (d: Distrib nF) : Prop where
  new_ne : d ≠ (g p)
  total_eq : d.total = (g p).total

theorem distrib_valid_iff (d: Distrib nF) : g.distrib_valid p d ↔
  d ≠ (g p) ∧ d.total = (g p).total := {
    mp  := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩
    mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩
  }

instance : DecidablePred (g.distrib_valid p) :=
  fun a ↦ decidable_of_iff' _ (g.distrib_valid_iff p a)

def runDistrib (d: Distrib nF) (_: g.distrib_valid p d) : Game nP nF :=
  Function.update g p d
end Distrib

def valid (m: Move nP nF) : Prop :=
  m.rec (g.attack_valid p) (g.distrib_valid p)

instance : DecidablePred (g.valid p) := by
  rintro ⟨_|_⟩ <;> unfold Game.valid <;> exact inferInstance

def runMove (m: Move nP nF) (h : g.valid p m := by decide) : Game nP nF :=
  match m with
  | .attack a => g.runAttack p a h
  | .distrib d => g.runDistrib p d h

#eval
  let g: Game 2 5 := default
  let m: Move 2 5 := .attack <| .mk L L 1
  g.runMove 0 m
end Move
-- def Move.valid (g: Game nP nF) (p: Player nP) : Move nP nF → Prop
-- | attack a => sorry
-- | distrib d => sorry

-- structure Attack (g: Game nP nF) (p: Player nP) where
--   (s_from s_to : Side)
--   target : Player nP
--   target_ne : target ≠ p := by decide
--   from_nz : (g p).get s_from ≠ 0 := by decide
--   to_nz : (g target).get s_to ≠ 0 := by decide

-- structure Distrib (g: Game nP nF) (p: Player nP) where
--   new : Fingers nF
--   new_ne : new ≠ (g p)
--   total_eq : new.total = (g p).total := by decide

-- inductive Move (g: Game nP nF) (p: Player nP)
-- | attack (a: g.Attack p)
-- | distrib (d: g.Distrib p)

-- def runAttack (g: Game nP nF) (p: Player nP) (a: g.Attack p) : Game nP nF :=
--   Function.update g a.target <| (g a.target).recieve ((g p).get a.s_from) a.s_to

-- def runDistrib (g: Game nP nF) (p: Player nP) (d: g.Distrib p) : Game nP nF :=
--   Function.update g p d.new

-- def run (g: Game nP nF) (p: Player nP) (m: g.Move p) : Game nP nF :=
--   m.casesOn (g.runAttack p) (g.runDistrib p)

-- #eval @id (Id _) do
--   let mut g : Game 2 5 := default
--   let m : g.Move 0 := .attack <| .mk L L 1
--   g := g.run _ m
--   return g
