import Mathlib

class MyBoolAlg (α) [Sup α] [Inf α] [Bot α] [Top α] [HasCompl α] where
  sup_bot: ∀{a: α}, a ⊔ ⊥ = a
  inf_top: ∀{a: α}, a ⊓ ⊤ = a
  sup_comm: ∀{a b: α}, a ⊔ b = b ⊔ a
  inf_comm: ∀{a b: α}, a ⊓ b = b ⊓ a
  sup_distrib: ∀{a b c: α}, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)
  inf_distrib: ∀{a b c: α}, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
  sup_compl: ∀{a: α}, a ⊔ aᶜ = ⊤
  inf_compl: ∀{a: α}, a ⊓ aᶜ = ⊥
namespace MyBoolAlg
variable {α} [Sup α] [Inf α] [Bot α] [Top α] [HasCompl α] [MyBoolAlg α]
section Theorems
variable {a b c : α}
theorem eq_compl (hsup: a ⊔ b = ⊤) (hinf: a ⊓ b = ⊥) : b = aᶜ := calc b
  _ = b ⊓ ⊤ := inf_top.symm
  _ = b ⊓ (a ⊔ aᶜ) := congrArg _ sup_compl.symm
  _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_distrib
  _ = ⊥ ⊔ (b ⊓ aᶜ) := congrArg (· ⊔ _) <| inf_comm.trans hinf
  _ = (a ⊓ aᶜ) ⊔ (b ⊓ aᶜ) := congrArg (· ⊔ _) inf_compl.symm
  _ = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ b) := congrArg₂ _ inf_comm inf_comm
  _ = aᶜ ⊓ (a ⊔ b) := inf_distrib.symm
  _ = aᶜ ⊓ ⊤ := congrArg _ hsup
  _ = aᶜ := inf_top
theorem compl_compl : aᶜᶜ = a := eq_compl (sup_comm.trans sup_compl) (inf_comm.trans inf_compl) |>.symm
theorem top_inf : ⊤ ⊓ a = a := inf_comm.trans inf_top
theorem bot_sup : ⊥ ⊔ a = a := sup_comm.trans sup_bot
theorem sup_self : a ⊔ a = a := calc
  _ = (a ⊔ a) ⊓ ⊤ := inf_top.symm
  _ = (a ⊔ a) ⊓ (a ⊔ aᶜ) := congrArg _ sup_compl.symm
  _ = a ⊔ (a ⊓ aᶜ) := sup_distrib.symm
  _ = a ⊔ ⊥ := congrArg _ inf_compl
  _ = a := sup_bot
theorem inf_self : a ⊓ a = a := calc
  _ = (a ⊓ a) ⊔ ⊥ := sup_bot.symm
  _ = (a ⊓ a) ⊔ (a ⊓ aᶜ) := congrArg _ inf_compl.symm
  _ = a ⊓ (a ⊔ aᶜ) := inf_distrib.symm
  _ = a ⊓ ⊤ := congrArg _ sup_compl
  _ = a := inf_top

theorem sup_assoc : a ⊔ (b ⊔ c) = a ⊔ b ⊔ c := calc a ⊔ (b ⊔ c)
  -- _ = ⊤ ⊓ (a ⊔ (b ⊔ c)) := inf_top.symm.trans inf_comm
  -- _ = (⊤ ⊓ a) ⊔ (⊤ ⊓ (b ⊔ c)) := sorry
  -- _ = a ⊔ (⊤ ⊓ (b ⊔ c)) := congrArg _ top_inf.symm
  -- _ = a ⊔ ((b ⊔ bᶜ) ⊓ (b ⊔ c)) := congr(a ⊔ ($(sup_compl.symm) ⊓ _))
  -- _ = a ⊔ (b ⊔ (bᶜ ⊓ c)) := congrArg _ sup_distrib.symm
  -- _ = (a ⊔ (b ⊔ bᶜ)) ⊓ (a ⊔ (b ⊔ c)) := sorry

  -- _ = a ⊔ ((b ⊓ b) ⊔ (c ⊓ c)) := congrArg _ <| congrArg₂ _ inf_self.symm inf_self.symm
  -- _ = a ⊔ ((b ⊓ b ⊔ c) ⊓ (b ⊓ b ⊔ c)) := congrArg _ sup_distrib
  -- _ = (a ⊔ (b ⊓ b ⊔ c)) ⊓ (a ⊔ (b ⊓ b ⊔ c)) := sup_distrib
  -- _ = (a ⊔ (b ⊔ c)) ⊓ (a ⊔ (b ⊔ c)) := inf_self (a := b).symm ▸ inf_self (a := b).symm ▸ rfl
  _ = (a ⊔ (b ⊔ c)) ⊓ (a ⊔ (b ⊔ c)) := inf_self.symm
  _ = a ⊔ ((b ⊔ c) ⊓ (b ⊔ c)) := sup_distrib.symm
  -- _ = a
  _ = _ := sorry

end Theorems


instance : Preorder α where
  le a b := a ⊔ b = b
  -- lt := sorry
  le_refl _ := sup_self
  le_trans a b c (ha: a ⊔ b = b) (hb: b ⊔ c = c) := by
    change a ⊔ c = c
    have : (a ⊔ b) ⊔ c = c := ha.substr hb

    sorry
  -- lt_iff_le_not_le := sorry

instance : PartialOrder α where
  le_antisymm _a _b ha hb := hb.symm.trans <| sup_comm.trans ha

instance : Lattice α where
  sup := (· ⊔ ·)
  le_sup_left _ _ := sorry
  le_sup_right _ _ := sorry
  sup_le _a _b _c ha hb := sorry
  inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry

example : BooleanAlgebra α where
  sup := sorry
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  le_sup_inf := sorry
  compl := sorry
  sdiff := sorry
  himp := sorry
  top := sorry
  bot := sorry
  inf_compl_le_bot := sorry
  top_le_sup_compl := sorry
  le_top := sorry
  bot_le := sorry
  sdiff_eq := sorry
  himp_eq := sorry

-- example (inf sup : α → α → α) (bot top : α) (compl : α → α)
--   (sup_bot : ∀a, sup a bot = a) (inf_top : ∀a, inf a top = a)
--   (sup_comm : ∀a b, sup a b = sup b a) (inf_comm : ∀a b, inf a b = inf b a)
--   (sup_distrib : ∀a b c, sup a (inf b c) = inf (sup a b) (sup a c))
--   (inf_distrib : ∀a b c, inf a (sup b c) = sup (inf a b) (inf a c))
--   (sup_compl : ∀a, sup a (compl a) = top) (inf_compl : ∀a, inf a (compl a) = bot): BooleanAlgebra α where
--     le a b := sup a b = b
--     -- lt := sorry
--     le_refl a := calc (sup a a)
--       _ = sup (inf a top) (inf a top) := congrArg₂ sup (inf_top a).symm (inf_top a).symm
--       _ = inf a (sup top top) := inf_distrib .. |>.symm
--       -- _ = inf a top :=
--       _ = a := sorry
--     le_trans a b c (ha: sup a b = b) (hb: sup b c = c) := sorry
--     -- lt_iff_le_not_le := sorry
--     le_antisymm a b ha hb := ha.symm.trans (sup_comm _ _ |>.trans hb) |>.symm
--     le_sup_left a b := sorry
--     le_sup_right a b := sorry
--     sup := sorry
--     sup_le := sorry
--     inf := sorry
--     inf_le_left := sorry
--     inf_le_right := sorry
--     le_inf := sorry
--     le_sup_inf := sorry
--     compl := sorry
--     sdiff := sorry
--     himp := sorry
--     top := sorry
--     bot := sorry
--     inf_compl_le_bot := sorry
--     top_le_sup_compl := sorry
--     le_top := sorry
--     bot_le := sorry
--     sdiff_eq := sorry
--     himp_eq := sorry
