Writing little things (currently just proofs) in Lean 4 for learning purposes

Recommendation: if you're reading these proofs (especially if you're relatively new to Lean like me), don't just read the code! Go to [Lean 4 Web](https://live.lean-lang.org/) and paste it in (or use `Load from URL` with the raw link) so you can hover over things and see their type/doc blurbs— that sort of thing can _really_ help in a language where so much information is at the type level.

Currently includes:
- [Irrationality of the square root of two](Misc/SqrtTwoIrrational.lean)
    - [Irrationality of the nth root of two](Misc/NrtTwoIrrational.lean)
    - [Irrationality of the nth root of a prime](Misc/NrtPrimeIrrational.lean)
- [Infinitude of the primes](Misc/InfPrimes.lean)
- **\[ANNOTATED\]** [Irrational to an irrational power could be rational](Misc/IrrationalPowIrrationalRational.lean)
    - Contains the same proof twice, with the second one thoroughly commented for someone with a cursory knowledge of type theory/computational proof
- ["Who Killed Lefty"](Misc/WhoKilledLefty.lean): a neat little problem I saw
    - Notably includes actual definitions of relevant ideas (not just using Mathlib stuff)
- [Integers as equivalence classes of ordered pairs of naturals](Misc/IntAsOrderedPairs.lean)
- [Unit quaternions have real part zero and square to -1](Misc/UnitQuaternion.lean)
- [$\forall n:\Z, 42 \mid n ^ 7 - n$](Misc/42DvdNPow7MinusN.lean)

See also [my proofs](https://github.com/TheCob11/PaulinIntroToAbstractAlgebra) from an introductory Abstract Algebra book
