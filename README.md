Writing little things (mostly proofs) in Lean 4 for learning purposes

Recommendation: if you're reading these proofs (especially if you're relatively new to Lean like me), don't just read the code! Go to [Lean 4 Web](https://live.lean-lang.org/) and paste it in (or use `Load from URL` with the raw link) so you can hover over things and see their type/doc blurbs— that sort of thing can _really_ help in a language where so much information is at the type level.

### Currently includes:
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
- [FizzBuzz](Misc/FizzBuzz.lean) (lol)
- [Additive abelian groups admit a unique Z-Module structure](Misc/AddCommGroupZModule.lean)
- [Actions (group, monoid, ring(module)) are equivalent to homomorphisms to endomorphism structures](Misc/Actions.lean)
- [Diaconescu's theorem, deriving excluded middle from choice](Misc/Diaconescu.lean)
- [Playing around with limits in category theory](Misc/CategoricalLimits.lean) (not polished but somewhat presentable compared to the WIPs)

Also includes a bunch of other small and/or WIP things which may or may not get finished eventually, including:
- Various neural network/neural network-adjacent experiements based on a few papers: [NNet](Misc/NNet.lean), [NNetOld](Misc/NNetOld.lean), [FreeMonad](Misc/FreeMonad.lean), [Quiver](Misc/Quiver.lean)
- [WIP implementation of the Chopsticks game](Misc/Chopsticks.lean)
- and more (really, every file that isn't linked in the main list)

See also [my proofs](https://github.com/TheCob11/PaulinIntroToAbstractAlgebra) from (lecture notes of?) an introductory Abstract Algebra course
