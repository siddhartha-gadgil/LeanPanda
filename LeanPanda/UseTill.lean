import Lean
import Mathlib
open Lean Meta Elab Tactic

/-!
We write a tactic that will automatically plug in values of Nat up to a fixed value and try a tactic.
-/
example : ∃ n: Nat, n * n + n = 20 ∧ n > 3 := by
  use 4
  simp

/-!
A tactic state has one or more goals. We can use `getGoals` to get the goals. If there are no goals, we are done.
-/

elab "use_till" n:num "then" tac:tacticSeq : tactic =>
  withMainContext do
  -- for now, we check up to 10
  let n := n.getNat
  let s₀ ← saveState -- save the state
  for i in [0:n] do
    let s ← saveState -- save the state
    try
      let iLit := Syntax.mkNumLit (toString i)
      let useTac ← `(tactic|use $iLit:term)
      evalTactic useTac
      if (← getGoals).isEmpty then
        return
      else
        evalTactic tac
        if (← getGoals).isEmpty then
          return
        throwError s!"use_till failed for {i}"
    catch _ =>
      restoreState s -- restore the state
  restoreState s₀
  throwError "use_till failed"
  return

example : ∃ n: Nat, n * n + n = 20 ∧ n > 3 := by
  use_till 10 then decide

/-!
Our tactic only checks if **all** the goals are solved. We should check if the main goal is solved.

We will fix this using `checkTactic` to check if a tactic works on a goal.
-/
/-- error: use_till failed -/
#guard_msgs in
example : (∃ n: Nat, n * n + n = 20 ∧ n > 3) ∧ True := by
  apply And.intro
  use_till 10 then decide
  trivial
