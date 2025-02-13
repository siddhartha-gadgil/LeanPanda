import Lean
open Lean Meta Elab Tactic
/-!
We make a `ToDo` tactic that is just like `sorry` except with extra syntax. We say `ToDo` followed by a string.

We will make this using `elab`. This means that we modify tactic state.
-/

elab "ToDo" t:str : tactic =>
  withMainContext do
  let α ← getMainTarget -- type of the current goal
  logInfo m!"To do: {t} to prove {α}"
  -- we want to create an expression of type `α` using `sorryAx`
  -- For this, Lean provides nice ways to make expressions:
  let pf ← mkAppM ``sorryAx #[α, mkConst ``false] -- `mkAppM` is a fancy way to apply a function to arguments
  closeMainGoal `ToDo pf
  return

example : 1 ≤ 3 := by
  ToDo "prove this"

#check Tactic.closeMainGoal

/-
sorryAx.{u} (α : Sort u) (synthetic : Bool) : α
-/
#check sorryAx
