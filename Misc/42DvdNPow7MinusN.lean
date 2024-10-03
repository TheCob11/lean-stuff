import Mathlib
open Int

lemma Int.dvd_pow_sub_self_of_ZMod_pow_eq {n: ℤ} {m p : ℕ}
  (h: (n: ZMod p) ^ m = n) : ↑p ∣ n ^ m - n :=
  ZMod.intCast_eq_intCast_iff_dvd_sub .. |>.mp <| (cast_npow ..).trans h |>.symm

variable {n: ℤ}

lemma even : Even (n ^ 7 - n) := match n.even_or_odd with
| .inl he => even_pow' (Nat.succ_ne_zero 6) |>.mpr he |>.sub he
| .inr ho => ho.pow.sub_odd ho

lemma three_dvd : 3 ∣ n ^ 7 - n := dvd_pow_sub_self_of_ZMod_pow_eq <|
  -- apparently i can do this with 7 and 6 too but that feels like cheating
  -- for some reason the same thing doesn't exactly work with 42 alone though
  match (n: ZMod 3) with | 0|1|2 => rfl

lemma seven_dvd : 7 ∣ n ^ 7 - n := dvd_pow_sub_self_of_ZMod_pow_eq <|
  @ZMod.pow_card 7 (by decide) n

lemma six_dvd : 6 ∣ n ^ 7 - n :=
  have : IsCoprime (2: ℤ) 3 := coprime_iff_nat_coprime.mpr rfl
  this.mul_dvd even.two_dvd three_dvd

theorem fourty_two_dvd : 42 ∣ n ^ 7 - n :=
  have : IsCoprime (6: ℤ) 7 := coprime_iff_nat_coprime.mpr rfl
  this.mul_dvd six_dvd seven_dvd

-- inlined proof using just cases for mod 6 and mod 7
example : 42 ∣ n ^ 7 - n :=
  have six_dvd : 6 ∣ n ^ 7 - n := dvd_pow_sub_self_of_ZMod_pow_eq <|
    match (n: ZMod 6) with | 0|1|2|3|4|5 => rfl
  have seven_dvd : 7 ∣ n ^ 7 - n := dvd_pow_sub_self_of_ZMod_pow_eq <|
    match (n: ZMod 7) with | 0|1|2|3|4|5|6 => rfl
  have : IsCoprime (6: ℤ) 7 := coprime_iff_nat_coprime.mpr rfl
  this.mul_dvd six_dvd seven_dvd

-- less clean but working version of the proof by cases for 42 entirely
example : 42 ∣ n ^ 7 - n := ZMod.intCast_eq_intCast_iff_dvd_sub .. |>.mp <| by
  mod_cases n % 42 <;> exact
    cast_pow (R := ZMod 42) .. ▸ (ZMod.intCast_eq_intCast_iff ..).mpr H ▸ rfl
