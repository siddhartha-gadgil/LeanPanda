import Lean
open Lean Meta Elab Tactic

/-!
# Rewriting inequalities for natural numbers.

If our goal is an inequality `a ≤ b` and a term `h : a ≤  c`, we can rewrite the inequality to `c ≤ b`. Here, we assume `a`, `b`, and `c` are natural numbers.

More generally, we try to rewrite given `h : c ≤ d` in various cases.

Our first step is to *recognize* the inequality.
* We set up an *equation* in variables (actually *metavariables*) and get Lean to solve it.
-/
def getNatIneq (e : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let natType := mkConst ``Nat
  let a ← mkFreshExprMVar natType -- metavariable, , i.e., an unknown of type `Nat`
  let b ← mkFreshExprMVar natType
  let ineq ← mkAppM ``Nat.le #[a, b]
  if ← isDefEq e ineq then -- `isDefEq` checks if two expressions are definitionally equal. It tries to "solve" the equation, i.e., assign metavariables so that the sides become equal.
    return some (a, b)
  else
    return none

elab "check_leq" : tactic => do
  let e ← getMainTarget
  match ← getNatIneq e with
  | some (a, b) =>
    logInfo m!"Recognized inequality: {a} ≤ {b}"
    return
  | none =>
    logWarning "Not a recognized inequality"
    return

example : 3 ≤ 6 := by
  check_leq
  sorry

example : 3 = 6 := by
  check_leq
  sorry

example : 3 > 6 + 1 := by
  check_leq
  sorry

elab "rw_nat_le" h:term strict?:("strict")? : tactic => withMainContext do
  let strict := strict?.isSome -- this means the other case too
  let h ← elabTerm h none
  let hType ← inferType h
  match ← getNatIneq hType with
  | some (c, d) => -- we have `h: c ≤ d`
    let e ← getMainTarget
    match ← getNatIneq e with
    | some (a, b) =>
      -- We should check if `a = c` and/or `b = d` and rewrite the inequality accordingly.
      let leftCheck ← isDefEq a c
      let rightCheck ← isDefEq b d
      if leftCheck && rightCheck then
        closeMainGoal `rw_nat_le h
        return
      if leftCheck then
        -- we have to show `d ≤ b`.
        let newTarget ← mkAppM ``Nat.le #[d, b]
        let newGoal ← mkFreshExprMVar newTarget -- metavariable for the new goal
        -- We prove the old goal using the hypothesis `h: a ≤ d` and the new goal.
        let pf ← mkAppM ``Nat.le_trans #[h, newGoal]
        let goal ← getMainGoal
        goal.assign pf
        replaceMainGoal [newGoal.mvarId!]
        return
    | none =>
      throwError s!"Goal not a recognized inequality {e}"
  | none =>
    throwError s!"Hypothesis not a recognized inequality: {h}"

/-!
## Exercises

* Do the other case: `d= b`
* Have a variant where if we do not have either match, we get two inequalities `a ≤ c` and `d ≤ b` as the new goals.
-/

#check assignExp

example (h : 3 ≤ 5) : 3 ≤ 6 := by
  rw_nat_le h strict
  simp
