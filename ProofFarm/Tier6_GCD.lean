/-
  ProofFarm.Tier6_GCD
  Greatest common divisor and coprimality.
-/
import ProofFarm.Tier5_Lists

namespace ProofFarm.GCD

-- ============================================================
-- GCD DEFINITION AND BASIC PROPERTIES
-- ============================================================

/-- Our own GCD via Euclidean algorithm with fuel. -/
def gcd : Nat → Nat → Nat
  | 0, b => b
  | a + 1, b => gcd (b % (a + 1)) (a + 1)
termination_by a => a
decreasing_by
  apply Nat.mod_lt
  omega

/-- Bridge: our gcd equals Lean's built-in Nat.gcd. -/
theorem gcd_eq_nat_gcd (a b : Nat) : gcd a b = Nat.gcd a b := by
  match a with
  | 0 => simp [gcd, Nat.gcd]
  | a + 1 => rw [gcd, Nat.gcd]; exact gcd_eq_nat_gcd (b % (a + 1)) (a + 1)
termination_by a
decreasing_by apply Nat.mod_lt; omega

/-- GCD with zero on the left. -/
-- ENGLISH: The GCD of 0 and b is b.
theorem gcd_zero_left (b : Nat) : gcd 0 b = b := by
  --PROOF_START[gcd_zero_left]
  simp [gcd]
  --PROOF_END[gcd_zero_left]

/-- GCD with zero on the right. -/
-- ENGLISH: The GCD of a and 0 is a.
theorem gcd_zero_right (a : Nat) : gcd a 0 = a := by
  --PROOF_START[gcd_zero_right]
  rw [gcd_eq_nat_gcd]; simp
  --PROOF_END[gcd_zero_right]

/-- GCD of a number with itself. -/
-- ENGLISH: The GCD of a number with itself is that number.
theorem gcd_self (n : Nat) : gcd n n = n := by
  --PROOF_START[gcd_self]
  rw [gcd_eq_nat_gcd]; exact Nat.gcd_self n
  --PROOF_END[gcd_self]

/-- GCD with one. -/
-- ENGLISH: The GCD of any number and 1 is 1.
theorem gcd_one_right (a : Nat) : gcd a 1 = 1 := by
  --PROOF_START[gcd_one_right]
  rw [gcd_eq_nat_gcd]; simp
  --PROOF_END[gcd_one_right]

-- ============================================================
-- GCD DIVIDES BOTH ARGUMENTS
-- ============================================================

/-- The GCD divides the first argument. -/
-- ENGLISH: The GCD of a and b always divides a.
theorem gcd_dvd_left (a b : Nat) : gcd a b ∣ a := by
  --PROOF_START[gcd_dvd_left]
  rw [gcd_eq_nat_gcd]; exact Nat.gcd_dvd_left a b
  --PROOF_END[gcd_dvd_left]

/-- The GCD divides the second argument. -/
-- ENGLISH: The GCD of a and b always divides b.
theorem gcd_dvd_right (a b : Nat) : gcd a b ∣ b := by
  --PROOF_START[gcd_dvd_right]
  rw [gcd_eq_nat_gcd]; exact Nat.gcd_dvd_right a b
  --PROOF_END[gcd_dvd_right]

/-- The GCD is the greatest common divisor: any common divisor divides it. -/
-- ENGLISH: If d divides both a and b, then d divides gcd(a, b).
theorem dvd_gcd (d a b : Nat) (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ gcd a b := by
  --PROOF_START[dvd_gcd]
  rw [gcd_eq_nat_gcd]; exact Nat.dvd_gcd h1 h2
  --PROOF_END[dvd_gcd]

-- ============================================================
-- GCD ALGEBRAIC PROPERTIES
-- ============================================================

/-- GCD is commutative. -/
-- ENGLISH: gcd(a, b) = gcd(b, a).
theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := by
  --PROOF_START[gcd_comm]
  simp [gcd_eq_nat_gcd, Nat.gcd_comm]
  --PROOF_END[gcd_comm]

/-- GCD is idempotent. -/
-- ENGLISH: gcd(a, a) = a.
theorem gcd_idem (a : Nat) : gcd a a = a := by
  --PROOF_START[gcd_idem]
  exact gcd_self a
  --PROOF_END[gcd_idem]

/-- GCD is positive when at least one argument is positive. -/
-- ENGLISH: If a or b is positive, their GCD is positive.
theorem gcd_pos (a b : Nat) (h : 0 < a ∨ 0 < b) : 0 < gcd a b := by
  --PROOF_START[gcd_pos]
  rw [gcd_eq_nat_gcd]
  cases h with
  | inl ha => exact Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega))
  | inr hb => exact Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (by omega))
  --PROOF_END[gcd_pos]

-- ============================================================
-- COPRIMALITY
-- ============================================================

/-- Two numbers are coprime when their GCD is 1. -/
def Coprime (a b : Nat) : Prop := gcd a b = 1

/-- Consecutive numbers are coprime. -/
-- ENGLISH: Any number and its successor share no common factor other than 1.
theorem coprime_succ (n : Nat) : Coprime n (n + 1) := by
  --PROOF_START[coprime_succ]
  unfold Coprime; rw [gcd_eq_nat_gcd]; simp [Nat.Coprime]
  --PROOF_END[coprime_succ]

/-- 1 is coprime to everything. -/
-- ENGLISH: 1 shares no common factor with any number (other than 1 itself).
theorem coprime_one_left (n : Nat) : Coprime 1 n := by
  --PROOF_START[coprime_one_left]
  unfold Coprime; rw [gcd_eq_nat_gcd]; simp
  --PROOF_END[coprime_one_left]

/-- Coprimality is symmetric. -/
-- ENGLISH: If a is coprime to b, then b is coprime to a.
theorem coprime_comm (a b : Nat) : Coprime a b → Coprime b a := by
  --PROOF_START[coprime_comm]
  unfold Coprime; intro h; rw [gcd_eq_nat_gcd] at *; rw [Nat.gcd_comm]; exact h
  --PROOF_END[coprime_comm]

/-- Coprime numbers have no common factor > 1. -/
-- ENGLISH: If a and b are coprime and d divides both, then d = 1.
theorem eq_one_of_coprime_dvd (a b d : Nat) (hc : Coprime a b) (h1 : d ∣ a) (h2 : d ∣ b) (hd : 0 < d) : d = 1 := by
  --PROOF_START[eq_one_of_coprime_dvd]
  unfold Coprime at hc
  have hdvd := dvd_gcd d a b h1 h2
  rw [hc] at hdvd
  exact Nat.le_antisymm (Nat.le_of_dvd (by omega) hdvd) hd
  --PROOF_END[eq_one_of_coprime_dvd]

-- ============================================================
-- GCD AND MULTIPLICATION
-- ============================================================

/-- GCD distributes over multiplication (one direction). -/
-- ENGLISH: gcd(k*a, k*b) = k * gcd(a, b) for any k.
theorem gcd_mul_left (k a b : Nat) : gcd (k * a) (k * b) = k * gcd a b := by
  --PROOF_START[gcd_mul_left]
  simp [gcd_eq_nat_gcd, Nat.gcd_mul_left]
  --PROOF_END[gcd_mul_left]

/-- If a and b are coprime, a divides b*c implies a divides c. -/
-- ENGLISH: If a and b share no common factor, and a divides b*c, then a must divide c alone.
theorem coprime_dvd_of_dvd_mul (a b c : Nat) (hc : Coprime a b) (h : a ∣ b * c) : a ∣ c := by
  --PROOF_START[coprime_dvd_of_dvd_mul]
  unfold Coprime at hc; rw [gcd_eq_nat_gcd] at hc
  exact Nat.Coprime.dvd_of_dvd_mul_left hc h
  --PROOF_END[coprime_dvd_of_dvd_mul]

/-- Product of coprime divisors divides. -/
-- ENGLISH: If a divides n and b divides n and a,b are coprime, then a*b divides n.
theorem coprime_mul_dvd (a b n : Nat) (hc : Coprime a b) (ha : a ∣ n) (hb : b ∣ n) : a * b ∣ n := by
  --PROOF_START[coprime_mul_dvd]
  unfold Coprime at hc; rw [gcd_eq_nat_gcd] at hc
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc ha hb
  --PROOF_END[coprime_mul_dvd]

end ProofFarm.GCD
