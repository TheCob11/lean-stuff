import Mathlib

namespace Chopsticks

inductive Side | L | R deriving Repr
open Side

structure Fingers (nF: ℕ) where
  (l r: ZMod nF)
  -- for eliminating redundancies
  (l_le_r : l.val ≤ r.val := by decide)
deriving Repr

namespace Fingers
abbrev get (f: Fingers nF) : Side → ZMod nF
| L => f.l | R => f.r

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

-- TODO Attack should enforce nonzero fingies
structure Attack (nP: ℕ) where
  s_from: Side
  target: Player nP
  s_to : Side

def Game.runAttack (g: Game nP nF) (p: Player nP) (a: Attack nP) : Game nP nF :=
  Function.update g a.target <| (g a.target).recieve ((g p).get a.s_from) a.s_to

-- TODO distrib should enforce same number of fingies
def Game.runDistrib : Game nP nF → Player nP → Fingers nF → Game nP nF :=
  Function.update

inductive Move (nP nF : ℕ)
| attack (a: Attack nP)
| distrib (new: Fingers nF)

-- inductive Game.Move2 (g: Game nP nF) (p: Player nP)
-- | attack (a: Attack nP) (from_nz: (g p).get s_from ≠ 0) (to_nz: (g ))

def Game.run (g: Game nP nF) (p: Player nP) (m: Move nP nF) : Game nP nF :=
  m.casesOn (g.runAttack p) (g.runDistrib p)
