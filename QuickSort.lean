import Mathlib

/-!
# Quicksort: Sorting an List in Lean

* If a list is empty or has only one element, it is already sorted.
* Otherwise, we choose a pivot element and partition the list into two sublists: one with elements less than the pivot and one with elements greater than or equal to the pivot.

In Lean, we can prove that the result is sorted. We also need to show termination.
-/
variable {α : Type}[LinearOrder α]

abbrev below (pivot: α) (l: List α): List α :=
  l.filter (fun x => x < pivot)

abbrev above (pivot: α) (l: List α): List α :=
  l.filter (fun x => pivot ≤ x)

def quickSort (l: List α): List α :=
  match l with
  | [] => []
  | x :: ys =>
    -- We take `x` as the pivot element
    let left := below x ys
    let right := above x ys
    have :
      (below x ys).length < ys.length + 1 :=  Order.lt_add_one_iff.mpr (List.length_filter_le _ ys)
    have :
      (above x ys).length < ys.length + 1 := Order.lt_add_one_iff.mpr (List.length_filter_le _ ys)
    (quickSort left) ++ [x] ++ (quickSort right)
  termination_by l.length

/-
List.length_filter_le.{u_1} {α : Type u_1} (p : α → Bool) (l : List α) : (List.filter p l).length ≤ l.length
-/
#check List.length_filter_le


/-
[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]
-/
#eval quickSort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

/-!
We want to prove that the result of `quickSort` is sorted and that it is the same list as the input list.
-/

theorem quickSort_mem_iff_mem (a : α) (l: List α):
  a ∈ quickSort l ↔ a ∈ l :=
  by
    cases l with
    | nil =>
      simp [quickSort]
    | cons x xs =>
      simp [quickSort]
      have :
        (below x xs).length < xs.length + 1 :=  Order.lt_add_one_iff.mpr (List.length_filter_le _ xs)
      have :
        (above x xs).length < xs.length + 1 := Order.lt_add_one_iff.mpr (List.length_filter_le _ xs)
      have h₁ : a ∈ quickSort (below x xs) ↔ a ∈ below x xs := quickSort_mem_iff_mem a (below x xs)
      have h₂ : a ∈ quickSort (above x xs) ↔ a ∈ above x xs := quickSort_mem_iff_mem a (above x xs)
      simp [h₁, h₂]
      apply Iff.intro
      · intro h'
        cases h'
        · right
          rename_i h''
          simp [h'']
        · rename_i h''
          cases h''
          case inl h'' =>
            left
            simp [h'']
          case inr h'' =>
            right
            simp [h'']
      · intro h'
        cases h'
        case inl h'' =>
          simp [h'']
        case inr h''=>
          by_cases c: a < x
          · left
            simp [h'', c]
          · right
            right
            simp [h'', c, le_of_not_gt c]
    termination_by l.length
