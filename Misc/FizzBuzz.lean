import Mathlib

structure FizzBuzz (α Word) where
  divisors: List (α × Word)

namespace FizzBuzz
def Response {_self: FizzBuzz α Word} := List Word ⊕ α

instance [ToString α] [ToString Word] {self: FizzBuzz α Word} :
  ToString self.Response where toString
  | .inl l => .join <| l.map toString
  | .inr a => toString a

variable (self: FizzBuzz α Word) [Dvd α]

def runAt (a: α) [DecidablePred (· ∣ a)] : self.Response :=
  match self.divisors.filter (·.1 ∣ a) with
  | [] => .inr a
  | l => .inl <| l.map Prod.snd

variable [DecidableRel ‹Dvd α›.dvd]

def runOn : List α → List self.Response := List.map (self.runAt ·)

def runFrom [Preorder α] [SuccOrder α] (first : α) (len: ℕ) :
  List self.Response := self.runOn <| List.iterate SuccOrder.succ first len

end FizzBuzz

def Basic [NatCast R] : FizzBuzz R ({"Fizz", "Buzz"}: Set String) where
  divisors := [(3, ⟨"Fizz", .inl rfl⟩), (5, ⟨"Buzz", .inr rfl⟩)]

/-- info:
FizzBuzz
1
2
Fizz
4
Buzz
Fizz
7
8
Fizz
Buzz
11
Fizz
13
14
FizzBuzz -/
#guard_msgs in
#eval println! String.intercalate "\n" <| Basic.runFrom 0 16 |>.map toString

def Fuzz [ToString α] (as: List α) : FizzBuzz α {s // ∃a ∈ as, s = s!"Fuzz{a} "} where
  divisors := as.attach.map fun ⟨p, hp⟩ ↦ (p, ⟨_, ⟨p, ⟨hp, rfl⟩⟩⟩)

/-- info:
Fuzz5 ⏎
101
Fuzz3 ⏎
103
Fuzz13 ⏎
Fuzz3 Fuzz5 Fuzz7 ⏎
106
107
Fuzz3 ⏎
109
Fuzz5 Fuzz11 ⏎
Fuzz3 ⏎
Fuzz7 ⏎
113
Fuzz3 ⏎
Fuzz5 ⏎
116
Fuzz3 Fuzz13 ⏎
118
Fuzz7 ⏎
Fuzz3 Fuzz5 ⏎
Fuzz11 ⏎
122
Fuzz3 ⏎
124
Fuzz5 ⏎
Fuzz3 Fuzz7 ⏎
127
128
Fuzz3 ⏎
Fuzz5 Fuzz13 -/
#guard_msgs in
#eval let fb := Fuzz [3, 5, 7, 11, 13]
  println! String.intercalate "\n" <| fb.runFrom 100 31 |>.map toString
