/-
  ProofFarm.Tier2_Order
  Ordering, comparison, subtraction, min/max for natural numbers.
-/
import ProofFarm.Tier1_NatBasic

namespace ProofFarm.Order

-- ============================================================
-- BASIC ORDERING
-- ============================================================

/-- Every number is less than or equal to itself. -/
-- ENGLISH: Any number is at least as big as itself.
theorem le_refl (n : Nat) : n ≤ n := by
  --PROOF_START[le_refl]
  omega
  --PROOF_END[le_refl]

/-- Less-than-or-equal is transitive. -/
-- ENGLISH: If a ≤ b and b ≤ c, then a ≤ c.
theorem le_trans (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  --PROOF_START[le_trans]
  omega
  --PROOF_END[le_trans]

/-- Less-than-or-equal is antisymmetric. -/
-- ENGLISH: If a ≤ b and b ≤ a, then a = b.
theorem le_antisymm (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  --PROOF_START[le_antisymm]
  omega
  --PROOF_END[le_antisymm]

/-- Strict less-than implies less-than-or-equal. -/
-- ENGLISH: If a < b, then certainly a ≤ b.
theorem le_of_lt (a b : Nat) (h : a < b) : a ≤ b := by
  --PROOF_START[le_of_lt]
  omega
  --PROOF_END[le_of_lt]

/-- Chaining ≤ and < gives <. -/
-- ENGLISH: If a ≤ b and b < c, then a < c.
theorem lt_of_le_of_lt (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  --PROOF_START[lt_of_le_of_lt]
  omega
  --PROOF_END[lt_of_le_of_lt]

/-- No number is strictly less than itself. -/
-- ENGLISH: A number can never be smaller than itself.
theorem lt_irrefl (a : Nat) : ¬(a < a) := by
  --PROOF_START[lt_irrefl]
  omega
  --PROOF_END[lt_irrefl]

/-- Nothing is less than zero. -/
-- ENGLISH: Zero is the smallest natural number.
theorem not_lt_zero (n : Nat) : ¬(n < 0) := by
  --PROOF_START[not_lt_zero]
  omega
  --PROOF_END[not_lt_zero]

/-- Zero is less than or equal to everything. -/
-- ENGLISH: Zero is at most any natural number.
theorem zero_le (n : Nat) : 0 ≤ n := by
  --PROOF_START[zero_le]
  omega
  --PROOF_END[zero_le]

/-- Successor preserves ≤. -/
-- ENGLISH: If n ≤ m, then n+1 ≤ m+1.
theorem succ_le_succ (n m : Nat) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  --PROOF_START[succ_le_succ]
  omega
  --PROOF_END[succ_le_succ]

/-- Successor reflects ≤. -/
-- ENGLISH: If n+1 ≤ m+1, then n ≤ m.
theorem le_of_succ_le_succ (n m : Nat) (h : n + 1 ≤ m + 1) : n ≤ m := by
  --PROOF_START[le_of_succ_le_succ]
  omega
  --PROOF_END[le_of_succ_le_succ]

-- ============================================================
-- TRICHOTOMY AND DECIDABILITY
-- ============================================================

/-- Every pair of naturals satisfies a < b or b ≤ a. -/
-- ENGLISH: For any two numbers, either the first is smaller, or the second is at most the first.
theorem lt_or_ge (a b : Nat) : a < b ∨ b ≤ a := by
  --PROOF_START[lt_or_ge]
  omega
  --PROOF_END[lt_or_ge]

/-- Trichotomy: exactly one of a < b, a = b, or a > b holds. -/
-- ENGLISH: Any two numbers are either equal, or one is strictly bigger.
theorem lt_or_eq_or_gt (a b : Nat) : a < b ∨ a = b ∨ b < a := by
  --PROOF_START[lt_or_eq_or_gt]
  omega
  --PROOF_END[lt_or_eq_or_gt]

-- ============================================================
-- MIN AND MAX
-- ============================================================

/-- min is commutative. -/
-- ENGLISH: The minimum of a and b is the same as the minimum of b and a.
theorem min_comm (a b : Nat) : min a b = min b a := by
  --PROOF_START[min_comm]
  omega
  --PROOF_END[min_comm]

/-- max is commutative. -/
-- ENGLISH: The maximum of a and b is the same as the maximum of b and a.
theorem max_comm (a b : Nat) : max a b = max b a := by
  --PROOF_START[max_comm]
  omega
  --PROOF_END[max_comm]

/-- min a b ≤ a. -/
-- ENGLISH: The minimum of two numbers is at most the first one.
theorem min_le_left (a b : Nat) : min a b ≤ a := by
  --PROOF_START[min_le_left]
  omega
  --PROOF_END[min_le_left]

/-- min a b ≤ b. -/
-- ENGLISH: The minimum of two numbers is at most the second one.
theorem min_le_right (a b : Nat) : min a b ≤ b := by
  --PROOF_START[min_le_right]
  omega
  --PROOF_END[min_le_right]

/-- a ≤ max a b. -/
-- ENGLISH: Any number is at most the maximum of it and another number.
theorem le_max_left (a b : Nat) : a ≤ max a b := by
  --PROOF_START[le_max_left]
  omega
  --PROOF_END[le_max_left]

/-- b ≤ max a b. -/
-- ENGLISH: Any number is at most the maximum of another number and it.
theorem le_max_right (a b : Nat) : b ≤ max a b := by
  --PROOF_START[le_max_right]
  omega
  --PROOF_END[le_max_right]

-- ============================================================
-- SUBTRACTION
-- ============================================================

/-- Subtracting then adding cancels (when b ≤ a). -/
-- ENGLISH: If b is at most a, then (a - b) + b gives back a.
theorem sub_add_cancel (a b : Nat) (h : b ≤ a) : a - b + b = a := by
  --PROOF_START[sub_add_cancel]
  omega
  --PROOF_END[sub_add_cancel]

/-- Adding then subtracting cancels. -/
-- ENGLISH: (a + b) - b always gives back a.
theorem add_sub_cancel (a b : Nat) : (a + b) - b = a := by
  --PROOF_START[add_sub_cancel]
  omega
  --PROOF_END[add_sub_cancel]

end ProofFarm.Order
