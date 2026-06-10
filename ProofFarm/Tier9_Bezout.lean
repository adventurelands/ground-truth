/-
  ProofFarm.Tier9_Bezout
  Bezout's identity and modular multiplicative inverse.
  The bridge from GCD/coprimality to constructive modular arithmetic.
-/
import ProofFarm.Tier8_Fermat

namespace ProofFarm.Bezout

-- ============================================================
-- EXTENDED GCD (Nat version)
-- ============================================================

/-- Extended GCD: returns (g, x, y, sign) where
    if sign = true:  a * x = b * y + g
    if sign = false: b * y = a * x + g
    and g = gcd(a, b).
    We need the sign flag because Nat has no negatives. -/
def egcd : Nat → Nat → (Nat × Nat × Nat × Bool)
  | 0, b => (b, 0, 1, false)
  | a + 1, b =>
    let (g, x, y, s) := egcd (b % (a + 1)) (a + 1)
    let q := b / (a + 1)
    if s then
      (g, y + q * x, x, false)
    else
      (g, y + q * x, x, true)
termination_by a => a
decreasing_by
  apply Nat.mod_lt
  omega

-- ============================================================
-- BEZOUT HELPERS
-- ============================================================

/-- Nat subtraction cancellation: if a + c = b + c then a = b. -/
-- ENGLISH: You can cancel addition from both sides of an equation.
theorem add_right_cancel_nat (a b c : Nat) (h : a + c = b + c) : a = b := by
  --PROOF_START[add_right_cancel_nat]
  omega
  --PROOF_END[add_right_cancel_nat]

/-- Mul distributes over add on right. -/
-- ENGLISH: a * (b + c) = a * b + a * c.
theorem mul_add_nat (a b c : Nat) : a * (b + c) = a * b + a * c := by
  --PROOF_START[mul_add_nat]
  exact Nat.left_distrib a b c
  --PROOF_END[mul_add_nat]

/-- Division-mod relationship restated. -/
-- ENGLISH: b = (b / a) * a + b % a when a > 0.
theorem div_mod_eq (a b : Nat) (ha : 0 < a) : b = (b / a) * a + b % a := by
  --PROOF_START[div_mod_eq]
  have := Nat.div_add_mod b a
  rw [Nat.mul_comm] at this
  exact this.symm
  --PROOF_END[div_mod_eq]

/-- If a * x % n = 0 and gcd(a, n) = 1, then n divides x. -/
-- ENGLISH: If a and n are coprime and a*x is divisible by n, then x itself is divisible by n.
theorem coprime_dvd_of_mul_mod_zero (a x n : Nat) (hc : GCD.Coprime a n) (h : (a * x) % n = 0) : n ∣ x := by
  --PROOF_START[coprime_dvd_of_mul_mod_zero]
  unfold GCD.Coprime at hc
  rw [GCD.gcd_eq_nat_gcd] at hc
  have hcop : Nat.Coprime n a := by rw [Nat.Coprime]; rw [Nat.gcd_comm]; exact hc
  have hdvd : n ∣ a * x := Nat.dvd_of_mod_eq_zero h
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  --PROOF_END[coprime_dvd_of_mul_mod_zero]

-- Helper: if (r + s) % n = r with r < n and s < n, then s = 0
private theorem sum_mod_eq_fst_imp_snd_zero (r s n : Nat) (hr : r < n) (hs : s < n)
    (h : (r + s) % n = r) : s = 0 := by
  if hsum : r + s < n then
    rw [Nat.mod_eq_of_lt hsum] at h; omega
  else
    have hlt2n : r + s < 2 * n := by omega
    have : r + s - n < n := by omega
    -- (r + s) ≥ n, and h says (r+s) % n = r
    -- n divides (r+s) - r = s (since (r+s) % n = r means n | (r+s-r) = n | s ... not quite)
    -- Actually: (r+s) % n = r means r+s = n*q + r for some q
    -- So s = n*q, but s < n, so q = 0 and s = 0
    have key : n ∣ s := by
      have := Nat.div_add_mod (r + s) n
      -- r + s = n * ((r+s)/n) + (r+s) % n = n * ((r+s)/n) + r
      rw [h] at this
      -- this : r + s = n * ((r+s)/n) + r, so s = n * ((r+s)/n)
      have : s = n * ((r + s) / n) := by omega
      exact ⟨(r + s) / n, this⟩
    obtain ⟨q, hq⟩ := key
    have : q = 0 := by
      if hq0 : q = 0 then exact hq0
      else
        have : q ≥ 1 := by omega
        have : s ≥ n := by
          calc s = n * q := hq
          _ ≥ n * 1 := Nat.mul_le_mul_left n this
          _ = n := Nat.mul_one n
        omega
    rw [this, Nat.mul_zero] at hq; exact hq

-- Helper: n | d and 0 < d < n is impossible
private theorem not_dvd_of_pos_lt (n d : Nat) (hdvd : n ∣ d) (hpos : 0 < d) (hlt : d < n) : False := by
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k ≥ 1 := by
    if hk0 : k = 0 then rw [hk0, Nat.mul_zero] at hk; omega
    else omega
  have : d ≥ n := by
    calc d = n * k := hk
    _ ≥ n * 1 := Nat.mul_le_mul_left n hk1
    _ = n := Nat.mul_one n
  omega

-- ============================================================
-- INT BEZOUT IDENTITY (helper for modular inverse)
-- ============================================================

/-- Bezout's identity in Int: for any a, b, there exist s, t with a*s + b*t = gcd(a,b). -/
private theorem int_bezout (a b : Nat) : ∃ s t : Int, ↑a * s + ↑b * t = ↑(Nat.gcd a b) := by
  induction a, b using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n hm ih =>
    obtain ⟨s, t, hs⟩ := ih
    refine ⟨t - ↑(n / m) * s, s, ?_⟩
    rw [Nat.gcd_rec m n]
    have hmod : (↑(n % m) : Int) = ↑n - ↑m * ↑(n / m) := by
      have := Nat.div_add_mod n m; omega
    rw [hmod] at hs
    rw [Int.sub_mul] at hs
    rw [Int.mul_sub]
    rw [Int.mul_assoc] at hs
    omega

-- ============================================================
-- MODULAR INVERSE EXISTENCE
-- ============================================================

/-- The map x -> a*x % n is injective when gcd(a,n) = 1. -/
-- ENGLISH: If a and n are coprime, then different values of x give different values of a*x mod n.
theorem mul_mod_injective (a n : Nat) (hn : 0 < n) (hc : GCD.Coprime a n)
    (x y : Nat) (hx : x < n) (hy : y < n) (h : (a * x) % n = (a * y) % n) : x = y := by
  --PROOF_START[mul_mod_injective]
  unfold GCD.Coprime at hc; rw [GCD.gcd_eq_nat_gcd] at hc
  have hcop : Nat.Coprime n a := by rw [Nat.Coprime, Nat.gcd_comm]; exact hc
  -- If x = y we're done. If x < y or y < x, derive contradiction.
  if hxy : x = y then exact hxy
  else
    exfalso
    if hlt : x < y then
      have hpos : 0 < y - x := by omega
      have hbound : y - x < n := by omega
      have hdist : a * y = a * x + a * (y - x) := by
        rw [← Nat.left_distrib]; congr 1; omega
      have heq : (a * x + a * (y - x)) % n = (a * x) % n := by
        rw [← hdist]; exact h.symm
      rw [Nat.add_mod] at heq
      have hr : (a * x) % n < n := Nat.mod_lt _ hn
      have hs : (a * (y - x)) % n < n := Nat.mod_lt _ hn
      have hmod0 : (a * (y - x)) % n = 0 :=
        sum_mod_eq_fst_imp_snd_zero _ _ _ hr hs heq
      have hdvd : n ∣ a * (y - x) := Nat.dvd_of_mod_eq_zero hmod0
      have hdvd2 : n ∣ (y - x) := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
      exact not_dvd_of_pos_lt n (y - x) hdvd2 hpos hbound
    else
      have hlt2 : y < x := by omega
      have hpos : 0 < x - y := by omega
      have hbound : x - y < n := by omega
      have hdist : a * x = a * y + a * (x - y) := by
        rw [← Nat.left_distrib]; congr 1; omega
      have heq : (a * y + a * (x - y)) % n = (a * y) % n := by
        rw [← hdist]; exact h
      rw [Nat.add_mod] at heq
      have hr : (a * y) % n < n := Nat.mod_lt _ hn
      have hs : (a * (x - y)) % n < n := Nat.mod_lt _ hn
      have hmod0 : (a * (x - y)) % n = 0 :=
        sum_mod_eq_fst_imp_snd_zero _ _ _ hr hs heq
      have hdvd : n ∣ a * (x - y) := Nat.dvd_of_mod_eq_zero hmod0
      have hdvd2 : n ∣ (x - y) := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
      exact not_dvd_of_pos_lt n (x - y) hdvd2 hpos hbound
  --PROOF_END[mul_mod_injective]

/-- If a and n are coprime and n > 1, there exists b with a * b % n = 1. -/
-- ENGLISH: Every number coprime to n has a multiplicative inverse modulo n. This is the key to modular division.
theorem mod_inverse_exists (a n : Nat) (hn : 1 < n) (hc : GCD.Coprime a n) :
    ∃ b : Nat, b < n ∧ (a * b) % n = 1 := by
  --PROOF_START[mod_inverse_exists]
  unfold GCD.Coprime at hc; rw [GCD.gcd_eq_nat_gcd] at hc
  -- hc : Nat.gcd a n = 1
  have ⟨s, t, hbez⟩ := int_bezout a n
  rw [hc] at hbez
  -- hbez : ↑a * s + ↑n * t = ↑1
  let b := (s % (↑n : Int)).toNat
  have hnn : (0 : Int) ≤ s % (↑n : Int) := Int.emod_nonneg s (by omega)
  have hlt : s % (↑n : Int) < ↑n := Int.emod_lt_of_pos s (by omega)
  refine ⟨b, ?_, ?_⟩
  · -- b < n
    omega
  · -- (a * b) % n = 1
    -- Step 1: (↑a * s) % ↑n = 1 (in Int)
    have hmod_int : (↑a * s) % (↑n : Int) = 1 := by
      have : (↑a : Int) * s = 1 - ↑n * t := by omega
      rw [this, show (1 : Int) - ↑n * t = 1 + ↑n * (-t) from by rw [Int.mul_neg]; omega]
      rw [Int.add_mul_emod_self_left]
      show ↑(1 : Nat) % (↑n : Int) = ↑(1 : Nat)
      rw [← Int.natCast_emod]; simp [Nat.mod_eq_of_lt hn]
    -- Step 2: (↑a * (s % ↑n)) % ↑n = 1
    have hmod_int2 : (↑a * (s % (↑n : Int))) % (↑n : Int) = 1 := by
      rw [Int.mul_emod, Int.emod_emod_of_dvd s (Int.dvd_refl (↑n : Int)),
          ← Int.mul_emod]
      exact hmod_int
    -- Step 3: Convert Int result to Nat
    have hb_eq : (↑b : Int) = s % (↑n : Int) := Int.toNat_of_nonneg hnn
    have hab_int : (↑(a * b) : Int) = ↑a * (s % (↑n : Int)) := by
      rw [Int.natCast_mul a b, hb_eq]
    have key : (↑((a * b) % n) : Int) = 1 := by
      rw [Int.natCast_emod, hab_int]; exact hmod_int2
    omega
  --PROOF_END[mod_inverse_exists]

/-- The modular inverse is unique. -/
-- ENGLISH: There is exactly one inverse of a modulo n (in the range 0..n-1).
theorem mod_inverse_unique (a n b1 b2 : Nat) (hn : 0 < n) (hc : GCD.Coprime a n)
    (hb1 : b1 < n) (hb2 : b2 < n)
    (h1 : (a * b1) % n = 1) (h2 : (a * b2) % n = 1) : b1 = b2 := by
  --PROOF_START[mod_inverse_unique]
  exact mul_mod_injective a n hn hc b1 b2 hb1 hb2 (by rw [h1, h2])
  --PROOF_END[mod_inverse_unique]

-- ============================================================
-- BEZOUT'S IDENTITY
-- ============================================================

/-- Bezout's identity for coprime naturals: if gcd(a,b) = 1, there exist x, y
    with a * x % b = 1 (when b > 1). -/
-- ENGLISH: If two numbers share no common factor, you can find a multiplier that gives remainder 1. This is Bezout's identity, the foundation of modular arithmetic.
theorem bezout_coprime (a b : Nat) (hb : 1 < b) (hc : GCD.Coprime a b) :
    ∃ x : Nat, x < b ∧ (a * x) % b = 1 := by
  --PROOF_START[bezout_coprime]
  exact mod_inverse_exists a b hb hc
  --PROOF_END[bezout_coprime]

/-- Inverse times original gives 1 mod n. -/
-- ENGLISH: Multiplying a number by its modular inverse gives 1 (modulo n).
theorem mul_mod_inverse_one (a b n : Nat) (hn : 1 < n) (hc : GCD.Coprime a n)
    (hb : b < n) (hinv : (a * b) % n = 1) : (b * a) % n = 1 := by
  --PROOF_START[mul_mod_inverse_one]
  rw [Nat.mul_comm]; exact hinv
  --PROOF_END[mul_mod_inverse_one]

-- ============================================================
-- COPRIME MULTIPLICATION HELPERS
-- ============================================================

/-- If gcd(a, m) = 1 and gcd(a, n) = 1, then gcd(a, m*n) = 1. -/
-- ENGLISH: If a is coprime to both m and n, then a is coprime to their product.
theorem coprime_mul (a m n : Nat) (hm : GCD.Coprime a m) (hn : GCD.Coprime a n) :
    GCD.Coprime a (m * n) := by
  --PROOF_START[coprime_mul]
  unfold GCD.Coprime at *
  rw [GCD.gcd_eq_nat_gcd] at *
  exact Nat.Coprime.mul_right hm hn
  --PROOF_END[coprime_mul]

/-- Coprimality from prime: if p is prime and p does not divide a, then gcd(a, p) = 1. -/
-- ENGLISH: A prime that doesn't divide a number must be coprime to it.
theorem coprime_of_prime_not_dvd (p a : Nat) (hp : Primes.IsPrime p) (hnd : ¬(p ∣ a)) :
    GCD.Coprime a p := by
  --PROOF_START[coprime_of_prime_not_dvd]
  exact GCD.coprime_comm p a (Primes.coprime_of_prime_not_dvd p a hp hnd)
  --PROOF_END[coprime_of_prime_not_dvd]

/-- Modular cancellation: if a*b ≡ a*c (mod n) and gcd(a,n) = 1, then b ≡ c (mod n). -/
-- ENGLISH: You can cancel a coprime factor from both sides of a modular equation.
theorem mul_mod_cancel_of_coprime (a b c n : Nat) (hn : 0 < n) (hc : GCD.Coprime a n)
    (h : (a * b) % n = (a * c) % n) : b % n = c % n := by
  --PROOF_START[mul_mod_cancel_of_coprime]
  have hbn : b % n < n := Nat.mod_lt _ hn
  have hcn : c % n < n := Nat.mod_lt _ hn
  have hab : (a * b) % n = (a * (b % n)) % n := by
    rw [Nat.mul_mod a b n, Nat.mul_mod a (b % n) n, Nat.mod_mod]
  have hac : (a * c) % n = (a * (c % n)) % n := by
    rw [Nat.mul_mod a c n, Nat.mul_mod a (c % n) n, Nat.mod_mod]
  have h2 : (a * (b % n)) % n = (a * (c % n)) % n := by
    rw [← hab, ← hac]; exact h
  exact mul_mod_injective a n hn hc (b % n) (c % n) hbn hcn h2
  --PROOF_END[mul_mod_cancel_of_coprime]

end ProofFarm.Bezout
