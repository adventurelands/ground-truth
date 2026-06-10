/-
  ProofFarm.Tier5_Lists
  Structural induction on lists: length, append, reverse, map, filter.
-/
import ProofFarm.Tier4_Divisibility

namespace ProofFarm.Lists

-- ============================================================
-- LENGTH
-- ============================================================

/-- The empty list has length zero. -/
-- ENGLISH: An empty list contains zero elements.
theorem length_nil : ([] : List α).length = 0 := by
  --PROOF_START[length_nil]
  simp
  --PROOF_END[length_nil]

/-- Length of cons is one plus length of tail. -/
-- ENGLISH: Adding an element to a list increases its length by one.
theorem length_cons (x : α) (xs : List α) : (x :: xs).length = xs.length + 1 := by
  --PROOF_START[length_cons]
  simp
  --PROOF_END[length_cons]

/-- Length of append is sum of lengths. -/
-- ENGLISH: Concatenating two lists gives a list whose length is the sum of the original lengths.
theorem length_append (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length := by
  --PROOF_START[length_append]
  simp
  --PROOF_END[length_append]

/-- Length of reverse equals original length. -/
-- ENGLISH: Reversing a list doesn't change how many elements it has.
theorem length_reverse (xs : List α) : xs.reverse.length = xs.length := by
  --PROOF_START[length_reverse]
  simp
  --PROOF_END[length_reverse]

/-- Length of map equals original length. -/
-- ENGLISH: Applying a function to every element doesn't change the list's length.
theorem length_map (f : α → β) (xs : List α) : (xs.map f).length = xs.length := by
  --PROOF_START[length_map]
  simp
  --PROOF_END[length_map]

-- ============================================================
-- APPEND
-- ============================================================

/-- Appending the empty list on the right is identity. -/
-- ENGLISH: Concatenating an empty list onto the end does nothing.
theorem append_nil (xs : List α) : xs ++ [] = xs := by
  --PROOF_START[append_nil]
  simp
  --PROOF_END[append_nil]

/-- Appending the empty list on the left is identity. -/
-- ENGLISH: Concatenating an empty list onto the front does nothing.
theorem nil_append (xs : List α) : [] ++ xs = xs := by
  --PROOF_START[nil_append]
  simp
  --PROOF_END[nil_append]

/-- Append is associative. -/
-- ENGLISH: When concatenating three lists, grouping doesn't matter.
theorem append_assoc (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  --PROOF_START[append_assoc]
  simp
  --PROOF_END[append_assoc]

-- ============================================================
-- REVERSE
-- ============================================================

/-- Reversing an empty list gives an empty list. -/
-- ENGLISH: The reverse of nothing is nothing.
theorem reverse_nil : ([] : List α).reverse = [] := by
  --PROOF_START[reverse_nil]
  simp
  --PROOF_END[reverse_nil]

/-- Reversing twice gives back the original. -/
-- ENGLISH: If you reverse a list and then reverse it again, you get back what you started with.
theorem reverse_reverse (xs : List α) : xs.reverse.reverse = xs := by
  --PROOF_START[reverse_reverse]
  simp
  --PROOF_END[reverse_reverse]

/-- Reverse distributes over append. -/
-- ENGLISH: Reversing a concatenation is the same as concatenating the reverses in opposite order.
theorem reverse_append (xs ys : List α) : (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  --PROOF_START[reverse_append]
  simp
  --PROOF_END[reverse_append]

-- ============================================================
-- MAP
-- ============================================================

/-- Mapping over an empty list gives an empty list. -/
-- ENGLISH: Applying a function to every element of an empty list gives an empty list.
theorem map_nil (f : α → β) : ([] : List α).map f = [] := by
  --PROOF_START[map_nil]
  simp
  --PROOF_END[map_nil]

/-- Map distributes over append. -/
-- ENGLISH: Mapping over a concatenation is the same as concatenating the maps.
theorem map_append (f : α → β) (xs ys : List α) : (xs ++ ys).map f = xs.map f ++ ys.map f := by
  --PROOF_START[map_append]
  simp
  --PROOF_END[map_append]

/-- Mapping with identity does nothing. -/
-- ENGLISH: Applying the do-nothing function to every element doesn't change the list.
theorem map_id (xs : List α) : xs.map id = xs := by
  --PROOF_START[map_id]
  simp
  --PROOF_END[map_id]

/-- Map composition: mapping f then g is the same as mapping (g ∘ f). -/
-- ENGLISH: Applying f to every element then g is the same as applying g∘f in one pass.
theorem map_map (f : α → β) (g : β → γ) (xs : List α) : (xs.map f).map g = xs.map (g ∘ f) := by
  --PROOF_START[map_map]
  simp
  --PROOF_END[map_map]

-- ============================================================
-- FILTER
-- ============================================================

/-- Filtering an empty list gives an empty list. -/
-- ENGLISH: Filtering nothing gives nothing.
theorem filter_nil (p : α → Bool) : ([] : List α).filter p = [] := by
  --PROOF_START[filter_nil]
  simp
  --PROOF_END[filter_nil]

/-- Filter length is at most original length. -/
-- ENGLISH: Filtering can only remove elements, never add them.
theorem length_filter_le (p : α → Bool) (xs : List α) : (xs.filter p).length ≤ xs.length := by
  --PROOF_START[length_filter_le]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.filter]
    split
    · simp; omega
    · omega
  --PROOF_END[length_filter_le]

/-- Filtering with always-true gives back the original. -/
-- ENGLISH: If you keep everything, the list doesn't change.
theorem filter_true (xs : List α) : xs.filter (fun _ => true) = xs := by
  --PROOF_START[filter_true]
  induction xs with | nil => rfl | cons x xs ih => simp [List.filter, ih]
  --PROOF_END[filter_true]

/-- Filtering with always-false gives empty. -/
-- ENGLISH: If you keep nothing, you get an empty list.
theorem filter_false (xs : List α) : xs.filter (fun _ => false) = [] := by
  --PROOF_START[filter_false]
  induction xs with | nil => rfl | cons x xs ih => simp [List.filter, ih]
  --PROOF_END[filter_false]

end ProofFarm.Lists
