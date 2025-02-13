import Mathlib
#check Array.eraseIdx

-- example (n: Nat)(h : Nat.Prime n) : n + 1 ≤ 30 := by slim_check
-- example (n: Nat)(h : Nat.Prime n) : n % 2 = 1 := by slim_check
-- example (n: Nat)(h : Nat.Prime n) : n + 1 ≤ 300 :=
--   by slim_check (config := {maxSize := 1000, numInst := 1000})


variable {α : Type}[LinearOrder α][Inhabited α]

partial def quickSort (arr : Array α) : Array α :=
  if arr.size <= 1 then arr
  else
    let pivot := arr.get! (arr.size / 2)
    let left := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x >= pivot)
    (quickSort left).push pivot |>.append (quickSort right)

partial def quickSortTask (arr : Array α)(depth : Nat) : Task (Array α) :=
  match depth with
  | 0 => Task.spawn fun _ => (quickSort arr)
  | n + 1 =>
    let pivot := arr.get! (arr.size / 2)
    let left := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x < pivot)
    let right := (arr.eraseIdx! (arr.size / 2)).filter (fun x => x >= pivot)
    let leftTask := quickSortTask left n
    let rightTask := quickSortTask right n
    Task.bind (rightTask) (fun right =>
      leftTask.map fun left => (left.push pivot).append right)

partial def quickSortAsync (arr : Array α)(depth : Nat) : Array α :=
  (quickSortTask arr depth).get

example (h: 1 = 1): 1 = 1 := by
  assumption
