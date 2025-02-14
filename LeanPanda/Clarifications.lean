import Lean
import Mathlib
import Std

/-!
# Questions

* What is the `do` notation? What is `←`?
* What is an Expression?
* What were the fixes for yesterday's `quickSort`?
-/

/-!
## Do notation

This is a nice way to deal with `Monad`s. The most familiar monad is `Option`. We take an example with `Option`:
-/
/-
inductive Option.{u} : Type u → Type u
number of parameters: 1
constructors:
Option.none : {α : Type u} → Option α
Option.some : {α : Type u} → α → Option α
-/
#print Option
/-!
With Monads, we have `pure` and `bind`/`flatMap`. From these we get map. It is easier to use `do` notation.
-/
def doubleNat? (n? : Option Nat) : Option Nat :=
  n?.map fun n => n + n

#check Option.map

/-
some 6
-/
#eval doubleNat? (some 3)
/-
none
-/
#eval doubleNat? none

/-!
The `do` notation lets us go inside the monad. We can use `←` to get the value out of the monad.
-/
def doubleNat?' (n? : Option Nat) :
  Option Nat :=do
  let n ← n?
  return n + n -- or `pure (n + n)`

#eval doubleNat?' (some 3) -- some 6

def addNat? (n? m? : Option Nat) : Option Nat := do
  let n ← n?
  let m ← m?
  return n + m

def addNatComplicated? (n? m? : Option Nat) : Option Nat := do
  let n ← n?
  let sum := n + (← m?)
  let sum?  := return sum
  -- return ← sum?
  sum?

#eval addNatComplicated? (some 3) (some 4) -- some 7
#eval addNatComplicated? (some 3) none -- none

/-!
## State Monads

Tactics involve a series of Monads, all of which have `State` and `Reader` (for configuration). These are stacked on top of each other.

* `IO` Monad
* `CoreM` Monad
* `MetaM` Monad
* `TermElabM` Monad
* `TacticM` Monad

Each of these has a `State` and a `Reader`. The `State` is for the state of the computation, and the `Reader` is for the configuration.
-/

/-
@[reducible] def StateM.{u} : Type u → Type u → Type u :=
fun σ α ↦ StateT σ Id α
-/
#print StateM

/-
def StateT.{u, v} : Type u → (Type u → Type v) → Type u → Type (max u v) :=
fun σ m α ↦ σ → m (α × σ)
-/
#print StateT

open Lean Meta Elab Tactic

/-!
## Expressions

* A Lean program, term etc are `String`.
* The `Parser` converts the `String` to an `Syntax`. This can be of many kinds.
* The `Syntax` is converted to an `Expr` by an elaborator. This is the internal representation of a **term**.\


In meta-programming, we work with `Expr`s (or Syntax). We can use `Expr` to create new `Expr`s.

* A tactic is an element of `TacticM Unit`. It is a function from `Tactic.State` to `Tactic.State`.
-/
