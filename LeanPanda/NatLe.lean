import Mathlib
import LeanPanda.Basic
/-!
# Metaprogramming in Lean

Metaprogramming is programs that write/modify/read programs. To do this, we use the internal representation of Lean programs.

In Lean, a program and its components are internally represented at two levels:

* Syntax
* Expression

So we can do metaprogramming at two levels:
* Macros: work at the syntax level
* Elaboration: work at the expression level

We start with macros. As an example, we prove inequalities like `10 ≤ 20` using only the theorem `Nat.succ_le_succ` and `Nat.zero_le`.
-/

/-
Nat.succ_le_succ {n m : Nat} : n ≤ m → n.succ ≤ m.succ
-/
#check Nat.succ_le_succ

/-
Nat.zero_le (n : Nat) : 0 ≤ n
-/
#check Nat.zero_le


example : 3 ≤ 6 := by
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply Nat.zero_le

/-!
To do this in general, we use `repeat` and `first` tactic combinators.
-/

example : 3 ≤ 6 := by
  repeat apply Nat.succ_le_succ
  apply Nat.zero_le

example : 10 ≤ 20 := by
  repeat apply Nat.succ_le_succ
  apply Nat.zero_le

/-!
A little more challenging is to use only `Nat.le_step` and `Nat.le_refl`.
-/
example : 3 ≤ 6 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

example : 10 ≤ 20 := by
  repeat apply Nat.le_step
  sorry

/-!
We use `first`
-/

example : 10 ≤ 20 := by
  repeat (first | apply Nat.le_refl | apply Nat.le_step)

example : 12 ≤ 63 := by
  repeat (first | apply Nat.le_refl | apply Nat.le_step)

macro "nat_le" : tactic => do
  `(tactic| repeat (first | apply Nat.le_refl | apply Nat.le_step))

example : 12 ≤ 63 := by
  nat_le

/-!
We make this more general, allowing anything to be used repeatedly and any way to finish.
-/

macro "repeat_using" x:tacticSeq "finish" y:tacticSeq : tactic => do
  `(tactic| repeat (first | $y | $x))

example : 12 ≤ 63 := by
  repeat_using apply Nat.le_step finish apply Nat.le_refl

example : 10 ≤ 20 := by
  repeat_using apply Nat.succ_le_succ finish apply Nat.zero_le

example : 3 ≤ 6 := by
  #leansearch "If a natural number is less than or equal to another, then its successor is less than or equal to the successor of the other."
  sorry

#leansearch "If a natural number is less than or equal to another, then its successor is less than or equal to the successor of the other."

/-!
We shall see what syntax and expressions look like in Lean.
-/
#stx [10 ≤ 20]

#expr [(10 : Nat) ≤ 20]
