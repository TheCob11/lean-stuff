import Mathlib
--  **Question:**
--  Lefty, a leader of the underworld, was killed by one of his own band of four henchmen.
--  Detective Sharp interviewed the men and determined that all were lying except for one.
--  He deduced who killed Lefty on the basis of the following statements:
--    Sharky: Socko killed Lefty.
--    Fats: Muscles didn't kill Lefty.
--    Socko: Muscles was shooting craps with Sharky when Lefty was knocked off.
--    Muscles: Socko didn't kill Lefty.
--  Who did kill Lefty?

inductive Goon
| A -- Sharky
| B -- Fats
| C -- Socko
| D -- Muscles
open Goon

inductive Goon.Killed : Goon → Prop
structure Killer (g: Goon) : Prop where
  killed: g.Killed
  -- im pretty sure this is necessary to have only one solution
  unique: ∀g2: Goon, g2.Killed → g2 = g

-- Statements from Detective Sharp's interviews of the Goons
@[simp] def statement : Goon → Prop
| A => Killer C
| B => ¬Killer D
| C => ¬Killer D ∧ ¬Killer A
| D => ¬Killer C

-- Detective Sharp's theorem: given that all but one goon is lying,
-- it can be deduced that **Muscles killed Lefty**
theorem sharps_theorem (h: ∃!g: Goon, statement g) : Killer D :=
  let g := h.choose
  have liar (g2: Goon) (hg2: g2 ≠ g) : ¬statement g2 :=
    of_not_not (fun h2 ↦ hg2 (h.choose_spec.right g2 (of_not_not h2)))
  match g with
  | A|D => of_not_not (liar B noConfusion)
  | B|C => absurd (liar A noConfusion) (liar D noConfusion)
