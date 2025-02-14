import Std
/-!
## Fibonacci with StateM for remembering the previous values
-/
open Std

#check StateM
#check HashMap

def slowFib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => slowFib n + slowFib (n + 1)

-- #eval slowFib 10
-- #eval slowFib 34

/-! This is slow because we repeat the calculation of eg `fib 30` twice while calculating `fib 32` - once directly, and once for `fib 31`.

Here we have a simple solution of defining pairs. But in general, we want to remember the values we have already calculated. We can use `StateM` for this.
-/
/-!
Monad that remembers the previous values as a map. We define `fibM` to take values in this monad.
-/
abbrev FibStateM := StateM (HashMap Nat Nat)

def fibM (n : Nat) : FibStateM Nat := do
  let m ← get -- state: map of previous values
  match m.get? n with
  | some v => return v
  | none => do
    let v ←
      match n with
      | 0 => return 0
      | 1 => return 1
      | n + 2 => do
        let v1 ← fibM n
        let v2 ← fibM (n + 1)
        pure <| v1 + v2
    let m := m.insert n v
    set m
    return v

#eval (fibM 40).run' {}
