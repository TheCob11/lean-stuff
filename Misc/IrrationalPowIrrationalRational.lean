import Mathlib
-- i do not know how to name this
theorem exists_irrational_pow_not_irrational : ∃ p q, Irrational p ∧ Irrational q ∧ ¬Irrational (p ^ q) :=
  have _ := Classical.dec
  let x := √2 ^ √2;
  if h: ¬Irrational x then ⟨√2, √2, irrational_sqrt_two, irrational_sqrt_two, h⟩
  else
    have : x ^ √2 = 2 := calc
      _ = √2 ^ (√2 * √2) := (Real.rpow_mul (Real.sqrt_nonneg 2) √2 √2).symm
      _ = √2 ^ (2: ℝ) := (Real.mul_self_sqrt zero_le_two).symm ▸ rfl
      _ = _ := Real.rpow_two _ ▸ Real.sq_sqrt zero_le_two
    ⟨x, √2, not_not.mp h, irrational_sqrt_two, this.symm ▸ not_irrational_ofNat 2⟩


-- proving that an irrational to an irrational power could be rational
-- "there exists (real numbers) `p` and `q` such that `p` is irrational and `q` is irrational and `p ^ q` is _not_ irrational"
example : ∃ p q, Irrational p ∧ Irrational q ∧ ¬Irrational (p ^ q) :=
  have _ := Classical.dec -- treat everything as decidable so we can do cases on Irrational bc we don't need to actually compute stuff
  let x := √2 ^ √2; -- just abbreviating this
  -- dependent if-then-else gives us two branches w/the respective hypothesis in each
  -- specifically, we're doing cases on if x is not irrational (i.e. rational, but x is still a real number)
  if h: ¬Irrational x then
    -- easy case, x is rational so we just use it
    -- anonymously constructing the Exists bc it's kinda complicated:
    -- in order: p, q, Irrational p, Irrational q, ¬Irrational (p ^ q)
    ⟨√2, √2, irrational_sqrt_two, irrational_sqrt_two, h⟩
  else -- now h is `¬¬Irrational x` (the double not is a little weird but I'm dealing w/it so I can put the simple case first)
    -- proving that `x ^ √2 = 2` (not specifying an identifier assigns it to `this`)
    have : x ^ √2 = 2 := calc -- calc does "stepwise reasoning over transitive relations" (in this case the relation is `=`)
      -- `Real.rpow_mul` proves (given a proof that `a` is nonnegative) that `a ^ (b*c) = a ^ b ^ c`, so we use `Eq.symm` to go the other way around
      _ = √2 ^ (√2 * √2) := (Real.rpow_mul (Real.sqrt_nonneg 2) √2 √2).symm
      -- `Real.mul_self_sqrt` proves (given a proof that `a` is nonneg) that `√a * √a = a`
      -- `▸` is a macro that does fancy substitution, so we're substituting into `rfl` (which is justa proof of a=a for whatever a makes this work)
      _ = √2 ^ (2: ℝ) := (Real.mul_self_sqrt zero_le_two).symm ▸ rfl
      -- (the rhs in this final equality is 2, it's inferred by the type like everything else)
      -- using `Real.rpow_two` to turn the 2 in the exponent from Real to Nat so we can use `Real.sq_sqrt`
      _ = _ := Real.rpow_two √2 ▸ Real.sq_sqrt zero_le_two
    -- now that we've proven that, another long anonymous constructor:
    -- `x` is our `p` and `√2` is our `q`
    -- `not_not` is `¬¬a↔a`, and `Iff.mp` (modus ponens) turns `a↔b` into `a→b` so we can pass `h` into it to get a proof of `Irrational x`
    -- `irrational_sqrt_two` proves `q` (√2) is irrational like before,
    -- and finally we substitute the previously proven equality (flipped) into a proof that 2 is not irrational to prove `¬Irrational (p ^ q)`
    ⟨x, √2, not_not.mp h, irrational_sqrt_two, this.symm ▸ not_irrational_ofNat 2⟩
