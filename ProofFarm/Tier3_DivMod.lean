/-
  ProofFarm.Tier3_DivMod
  Division and modular arithmetic on natural numbers.
-/
import ProofFarm.Tier2_Order

namespace ProofFarm.DivMod

-- ============================================================
-- MODULAR ARITHMETIC
-- ============================================================

/-- Any number mod itself is zero. -/
-- ENGLISH: The remainder when dividing a number by itself is always zero.
theorem mod_self (n : Nat) : n % n = 0 := by
  --PROOF_START[mod_self]
  simp
  --PROOF_END[mod_self]

/-- Dividing by zero returns the number itself. -/
-- ENGLISH: n mod 0 is defined as n (division by zero is harmless in Nat).
theorem mod_zero (n : Nat) : n % 0 = n := by
  --PROOF_START[mod_zero]
  omega
  --PROOF_END[mod_zero]

/-- Zero mod anything is zero. -/
-- ENGLISH: The remainder when dividing zero by anything is zero.
theorem zero_mod (n : Nat) : 0 % n = 0 := by
  --PROOF_START[zero_mod]
  simp
  --PROOF_END[zero_mod]

/-- Anything mod 1 is zero. -/
-- ENGLISH: Every number is evenly divisible by 1.
theorem mod_one (n : Nat) : n % 1 = 0 := by
  --PROOF_START[mod_one]
  omega
  --PROOF_END[mod_one]

/-- The remainder is always less than the divisor (when divisor > 0). -/
-- ENGLISH: The remainder is always smaller than what you're dividing by.
theorem mod_lt (a b : Nat) (hb : 0 < b) : a % b < b := by
  --PROOF_START[mod_lt]
exact Nat.mod_lt _ hb
  --PROOF_END[mod_lt]

/-- Division/modulo relationship. -/
-- ENGLISH: Quotient times divisor plus remainder equals the original number.
theorem div_add_mod (a b : Nat) : b * (a / b) + a % b = a := by
  --PROOF_START[div_add_mod]
exact?
  --PROOF_END[div_add_mod]

/-- If a number is already smaller than the divisor, mod is identity. -/
-- ENGLISH: If a < b, then a mod b is just a.
theorem mod_eq_of_lt (a b : Nat) (h : a < b) : a % b = a := by
  --PROOF_START[mod_eq_of_lt]
exact?
  --PROOF_END[mod_eq_of_lt]

/-- Dividing a perfect multiple gives the multiplier. -/
-- ENGLISH: (b * a) / b = a, when b > 0.
theorem mul_div_cancel (a b : Nat) (hb : 0 < b) : (b * a) / b = a := by
  --PROOF_START[mul_div_cancel]
exact?
  --PROOF_END[mul_div_cancel]

/-- Modding a perfect multiple gives zero. -/
-- ENGLISH: (b * a) mod b = 0.
theorem mul_mod_cancel (a b : Nat) : (b * a) % b = 0 := by
  --PROOF_START[mul_mod_cancel]
  simp
  --PROOF_END[mul_mod_cancel]

-- ============================================================
-- MODULAR ARITHMETIC LAWS
-- ============================================================

/-- Addition distributes over mod. -/
-- ENGLISH: (a + b) mod n = ((a mod n) + (b mod n)) mod n.
theorem add_mod (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  --PROOF_START[add_mod]
  simp
  --PROOF_END[add_mod]

/-- Multiplication distributes over mod. -/
-- ENGLISH: (a * b) mod n = ((a mod n) * (b mod n)) mod n.
theorem mul_mod (a b n : Nat) : (a * b) % n = ((a % n) * (b % n)) % n := by
  --PROOF_START[mul_mod]
  simp
  --PROOF_END[mul_mod]

/-- Modding twice is the same as modding once. -/
-- ENGLISH: Taking the remainder twice doesn't change the result.
theorem mod_mod_self (a n : Nat) : (a % n) % n = a % n := by
  --PROOF_START[mod_mod_self]
  simp
  --PROOF_END[mod_mod_self]

/-- If a ≡ b (mod n) and b ≡ c (mod n), then a ≡ c (mod n). -/
-- ENGLISH: Modular equivalence is transitive.
theorem mod_trans (a b c n : Nat) (h1 : a % n = b % n) (h2 : b % n = c % n) : a % n = c % n := by
  --PROOF_START[mod_trans]
  omega
  --PROOF_END[mod_trans]

-- ============================================================
-- DIVISION PROPERTIES
-- ============================================================

/-- Zero divided by anything is zero. -/
-- ENGLISH: Dividing zero by any number gives zero.
theorem zero_div (n : Nat) : 0 / n = 0 := by
  --PROOF_START[zero_div]
  simp
  --PROOF_END[zero_div]

/-- Dividing by one is identity. -/
-- ENGLISH: Any number divided by 1 is itself.
theorem div_one (n : Nat) : n / 1 = n := by
  --PROOF_START[div_one]
  omega
  --PROOF_END[div_one]

/-- A number divided by itself is 1 (when positive). -/
-- ENGLISH: Any positive number divided by itself is 1.
theorem div_self (n : Nat) (hn : 0 < n) : n / n = 1 := by
  --PROOF_START[div_self]
  exact Nat.div_self hn
  --PROOF_END[div_self]

/-- Division makes things smaller (when divisor > 1). -/
-- ENGLISH: Dividing a positive number by something bigger than 1 makes it smaller.
theorem div_lt (a b : Nat) (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  --PROOF_START[div_lt]
  exact Nat.div_lt_self ha hb
  --PROOF_END[div_lt]

/-- Division is monotone. -/
-- ENGLISH: If a ≤ b, then a/n ≤ b/n.
theorem div_le_div (a b n : Nat) (h : a ≤ b) : a / n ≤ b / n := by
  --PROOF_START[div_le_div]
  exact Nat.div_le_div_right h
  --PROOF_END[div_le_div]

/-- Multiplication then division (exact). -/
-- ENGLISH: If n divides a, then (a / n) * n = a.
theorem div_mul_cancel_of_dvd (a n : Nat) (hn : 0 < n) (hd : n ∣ a) : (a / n) * n = a := by
  --PROOF_START[div_mul_cancel_of_dvd]
  exact Nat.div_mul_cancel hd
  --PROOF_END[div_mul_cancel_of_dvd]

end ProofFarm.DivMod
