/-
  ProofFarm.Tier1_NatBasic
  Basic natural number properties: addition, multiplication, cancellation.
  These are the foundation everything else builds on.
-/
namespace ProofFarm.Nat

-- ============================================================
-- ADDITION
-- ============================================================

/-- Zero plus any number is that number. -/
-- ENGLISH: Adding zero on the left does nothing.
theorem zero_add (n : Nat) : 0 + n = n := by
  --PROOF_START[zero_add]
omega
  --PROOF_END[zero_add]

/-- Any number plus zero is that number. -/
-- ENGLISH: Adding zero on the right does nothing.
theorem add_zero (n : Nat) : n + 0 = n := by
  --PROOF_START[add_zero]
omega
  --PROOF_END[add_zero]

/-- Successor on the left distributes into the sum. -/
-- ENGLISH: (n+1) + m is the same as (n + m) + 1.
theorem succ_add (n m : Nat) : (n + 1) + m = (n + m) + 1 := by
  --PROOF_START[succ_add]
  omega
  --PROOF_END[succ_add]

/-- Successor on the right distributes into the sum. -/
-- ENGLISH: n + (m+1) is the same as (n + m) + 1.
theorem add_succ (n m : Nat) : n + (m + 1) = (n + m) + 1 := by
  --PROOF_START[add_succ]
  omega
  --PROOF_END[add_succ]

/-- Addition is commutative. -/
-- ENGLISH: The order you add two numbers doesn't matter.
theorem add_comm (a b : Nat) : a + b = b + a := by
  --PROOF_START[add_comm]
  omega
  --PROOF_END[add_comm]

/-- Addition is associative. -/
-- ENGLISH: When adding three numbers, grouping doesn't matter.
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  --PROOF_START[add_assoc]
  omega
  --PROOF_END[add_assoc]

/-- Left cancellation for addition. -/
-- ENGLISH: If a + b = a + c, then b must equal c.
theorem add_left_cancel (a b c : Nat) (h : a + b = a + c) : b = c := by
  --PROOF_START[add_left_cancel]
  omega
  --PROOF_END[add_left_cancel]

/-- Right cancellation for addition. -/
-- ENGLISH: If a + c = b + c, then a must equal b.
theorem add_right_cancel (a b c : Nat) (h : a + c = b + c) : a = b := by
  --PROOF_START[add_right_cancel]
  omega
  --PROOF_END[add_right_cancel]

/-- If a + b = 0, then both a and b are 0. -/
-- ENGLISH: The only way two natural numbers sum to zero is if both are zero.
theorem eq_zero_of_add_eq_zero (a b : Nat) (h : a + b = 0) : a = 0 ∧ b = 0 := by
  --PROOF_START[eq_zero_of_add_eq_zero]
  omega
  --PROOF_END[eq_zero_of_add_eq_zero]

-- ============================================================
-- MULTIPLICATION
-- ============================================================

/-- Zero times anything is zero. -/
-- ENGLISH: Multiplying by zero on the left always gives zero.
theorem zero_mul (n : Nat) : 0 * n = 0 := by
  --PROOF_START[zero_mul]
  omega
  --PROOF_END[zero_mul]

/-- Anything times zero is zero. -/
-- ENGLISH: Multiplying by zero on the right always gives zero.
theorem mul_zero (n : Nat) : n * 0 = 0 := by
  --PROOF_START[mul_zero]
  omega
  --PROOF_END[mul_zero]

/-- One times anything is that number. -/
-- ENGLISH: Multiplying by one on the left does nothing.
theorem one_mul (n : Nat) : 1 * n = n := by
  --PROOF_START[one_mul]
  omega
  --PROOF_END[one_mul]

/-- Anything times one is that number. -/
-- ENGLISH: Multiplying by one on the right does nothing.
theorem mul_one (n : Nat) : n * 1 = n := by
  --PROOF_START[mul_one]
  omega
  --PROOF_END[mul_one]

/-- Successor distributes over multiplication on the left. -/
-- ENGLISH: (n+1) * m equals n*m + m.
theorem succ_mul (n m : Nat) : (n + 1) * m = n * m + m := by
  --PROOF_START[succ_mul]
  induction m with | zero => simp | succ m ih => simp [Nat.mul_succ, ih]; omega
  --PROOF_END[succ_mul]

/-- Successor distributes over multiplication on the right. -/
-- ENGLISH: n * (m+1) equals n*m + n.
theorem mul_succ (n m : Nat) : n * (m + 1) = n * m + n := by
  --PROOF_START[mul_succ]
  rfl
  --PROOF_END[mul_succ]

/-- Multiplication is commutative. -/
-- ENGLISH: The order you multiply two numbers doesn't matter.
theorem mul_comm (a b : Nat) : a * b = b * a := by
  --PROOF_START[mul_comm]
  induction a with | zero => simp | succ n ih => simp [succ_mul, Nat.mul_succ, ih]
  --PROOF_END[mul_comm]

/-- Multiplication is associative. -/
-- ENGLISH: When multiplying three numbers, grouping doesn't matter.
theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  --PROOF_START[mul_assoc]
  induction a with | zero => simp | succ n ih => simp [succ_mul, Nat.add_mul, ih]
  --PROOF_END[mul_assoc]

/-- Multiplication distributes over addition on the left. -/
-- ENGLISH: a * (b + c) equals a*b + a*c.
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  --PROOF_START[mul_add]
  induction a with | zero => simp | succ n ih => simp [succ_mul, ih, Nat.add_assoc]; omega
  --PROOF_END[mul_add]

/-- Multiplication distributes over addition on the right. -/
-- ENGLISH: (a + b) * c equals a*c + b*c.
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  --PROOF_START[add_mul]
  rw [mul_comm, mul_add]; simp [mul_comm]
  --PROOF_END[add_mul]

/-- If a product is zero, one of the factors must be zero. -/
-- ENGLISH: The only way to multiply two numbers and get zero is if one of them is zero.
theorem eq_zero_of_mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  --PROOF_START[eq_zero_of_mul_eq_zero]
  cases a with | zero => left; rfl | succ n => right; simp [succ_mul] at h; omega
  --PROOF_END[eq_zero_of_mul_eq_zero]

end ProofFarm.Nat
