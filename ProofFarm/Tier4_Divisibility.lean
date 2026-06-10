/-
  ProofFarm.Tier4_Divisibility
  Divisibility relation and its properties.
-/
import ProofFarm.Tier3_DivMod

namespace ProofFarm.Divisibility

-- ============================================================
-- BASIC DIVISIBILITY
-- ============================================================

/-- Every number divides itself. -/
-- ENGLISH: Any number is divisible by itself.
theorem dvd_refl (n : Nat) : n ∣ n := by
  --PROOF_START[dvd_refl]
  exact ⟨1, by simp⟩
  --PROOF_END[dvd_refl]

/-- One divides everything. -/
-- ENGLISH: Every number is divisible by 1.
theorem one_dvd (n : Nat) : 1 ∣ n := by
  --PROOF_START[one_dvd]
  exact ⟨n, by simp⟩
  --PROOF_END[one_dvd]

/-- Everything divides zero. -/
-- ENGLISH: Zero is divisible by every number.
theorem dvd_zero (n : Nat) : n ∣ 0 := by
  --PROOF_START[dvd_zero]
  exact ⟨0, by simp⟩
  --PROOF_END[dvd_zero]

/-- If zero divides n, then n is zero. -/
-- ENGLISH: The only number divisible by zero is zero itself.
theorem eq_zero_of_zero_dvd (n : Nat) (h : 0 ∣ n) : n = 0 := by
  --PROOF_START[eq_zero_of_zero_dvd]
  obtain ⟨k, hk⟩ := h; simp_all
  --PROOF_END[eq_zero_of_zero_dvd]

/-- Divisibility is transitive. -/
-- ENGLISH: If a divides b and b divides c, then a divides c.
theorem dvd_trans (a b c : Nat) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  --PROOF_START[dvd_trans]
  exact Nat.dvd_trans h1 h2
  --PROOF_END[dvd_trans]

/-- Any number divides its multiples. -/
-- ENGLISH: a always divides a * b.
theorem dvd_mul_right (a b : Nat) : a ∣ a * b := by
  --PROOF_START[dvd_mul_right]
  exact ⟨b, rfl⟩
  --PROOF_END[dvd_mul_right]

/-- Any number divides its multiples (other side). -/
-- ENGLISH: a always divides b * a.
theorem dvd_mul_left (a b : Nat) : a ∣ b * a := by
  --PROOF_START[dvd_mul_left]
  exact ⟨b, by simp [Nat.mul_comm]⟩
  --PROOF_END[dvd_mul_left]

/-- Divisibility iff mod is zero. -/
-- ENGLISH: a divides b exactly when b mod a is zero.
theorem dvd_iff_mod_eq_zero (a b : Nat) : a ∣ b ↔ b % a = 0 := by
  --PROOF_START[dvd_iff_mod_eq_zero]
  exact Nat.dvd_iff_mod_eq_zero
  --PROOF_END[dvd_iff_mod_eq_zero]

-- ============================================================
-- DIVISIBILITY AND ARITHMETIC
-- ============================================================

/-- Divisibility is preserved under addition. -/
-- ENGLISH: If d divides a and d divides b, then d divides a + b.
theorem dvd_add (d a b : Nat) (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a + b) := by
  --PROOF_START[dvd_add]
  obtain ⟨k1, hk1⟩ := h1; obtain ⟨k2, hk2⟩ := h2
  exact ⟨k1 + k2, by subst hk1; subst hk2; simp [Nat.mul_add]⟩
  --PROOF_END[dvd_add]

/-- Divisibility is preserved under subtraction (when b ≤ a). -/
-- ENGLISH: If d divides a and d divides b, then d divides a - b.
theorem dvd_sub (d a b : Nat) (h1 : d ∣ a) (h2 : d ∣ b) (hle : b ≤ a) : d ∣ (a - b) := by
  --PROOF_START[dvd_sub]
  rcases h1 with ⟨k1, rfl⟩; rcases h2 with ⟨k2, rfl⟩
  exact ⟨k1 - k2, (Nat.mul_sub d k1 k2).symm⟩
  --PROOF_END[dvd_sub]

/-- If d divides a, then d divides a * c. -/
-- ENGLISH: If you can divide a by d, you can also divide any multiple of a by d.
theorem dvd_mul_of_dvd_left (d a c : Nat) (h : d ∣ a) : d ∣ a * c := by
  --PROOF_START[dvd_mul_of_dvd_left]
  exact Nat.dvd_trans h ⟨c, rfl⟩
  --PROOF_END[dvd_mul_of_dvd_left]

/-- If d divides b, then d divides a * b. -/
-- ENGLISH: If d divides one factor, it divides the whole product.
theorem dvd_mul_of_dvd_right (d a b : Nat) (h : d ∣ b) : d ∣ a * b := by
  --PROOF_START[dvd_mul_of_dvd_right]
  exact Nat.dvd_trans h ⟨a, by simp [Nat.mul_comm]⟩
  --PROOF_END[dvd_mul_of_dvd_right]

-- ============================================================
-- DIVISIBILITY AND ORDERING
-- ============================================================

/-- A divisor of a positive number is at most that number. -/
-- ENGLISH: If d divides a and a > 0, then d ≤ a.
theorem le_of_dvd (d a : Nat) (ha : 0 < a) (h : d ∣ a) : d ≤ a := by
  --PROOF_START[le_of_dvd]
  exact Nat.le_of_dvd ha h
  --PROOF_END[le_of_dvd]

/-- If a divides b and b divides a, they're equal (for positive numbers). -/
-- ENGLISH: Two positive numbers that divide each other must be equal.
theorem dvd_antisymm (a b : Nat) (h1 : a ∣ b) (h2 : b ∣ a) : a = b := by
  --PROOF_START[dvd_antisymm]
  exact Nat.dvd_antisymm h1 h2
  --PROOF_END[dvd_antisymm]

/-- If d divides a and a < d, then a = 0. -/
-- ENGLISH: A number smaller than its divisor must be zero.
theorem eq_zero_of_dvd_of_lt (d a : Nat) (hd : d ∣ a) (hlt : a < d) : a = 0 := by
  --PROOF_START[eq_zero_of_dvd_of_lt]
  cases a with
  | zero => rfl
  | succ n => exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  --PROOF_END[eq_zero_of_dvd_of_lt]

-- ============================================================
-- EVEN AND ODD
-- ============================================================

/-- Definition of even via divisibility. -/
-- ENGLISH: A number is even if and only if 2 divides it.
theorem even_iff_dvd (n : Nat) : (∃ k, n = 2 * k) ↔ 2 ∣ n := by
  --PROOF_START[even_iff_dvd]
  constructor
  · intro ⟨k, hk⟩; exact ⟨k, hk⟩
  · intro ⟨k, hk⟩; exact ⟨k, hk⟩
  --PROOF_END[even_iff_dvd]

/-- The sum of two even numbers is even. -/
-- ENGLISH: Adding two even numbers always gives an even number.
theorem even_add_even (a b : Nat) (ha : 2 ∣ a) (hb : 2 ∣ b) : 2 ∣ (a + b) := by
  --PROOF_START[even_add_even]
  obtain ⟨k1, hk1⟩ := ha; obtain ⟨k2, hk2⟩ := hb
  exact ⟨k1 + k2, by subst hk1; subst hk2; simp [Nat.mul_add]⟩
  --PROOF_END[even_add_even]

/-- An even number times anything is even. -/
-- ENGLISH: Multiplying an even number by anything gives an even number.
theorem even_mul (a b : Nat) (ha : 2 ∣ a) : 2 ∣ (a * b) := by
  --PROOF_START[even_mul]
  exact Nat.dvd_trans ha ⟨b, rfl⟩
  --PROOF_END[even_mul]

/-- Every number is either even or odd. -/
-- ENGLISH: Every natural number leaves remainder 0 or 1 when divided by 2.
theorem even_or_odd (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  --PROOF_START[even_or_odd]
  omega
  --PROOF_END[even_or_odd]

end ProofFarm.Divisibility
