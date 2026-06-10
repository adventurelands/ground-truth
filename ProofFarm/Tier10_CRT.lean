/-
  ProofFarm.Tier10_CRT
  Chinese Remainder Theorem: reconstructing integers from residues.
  One of the oldest algorithms in mathematics (Sun Zi, 3rd century).
-/
import ProofFarm.Tier9_Bezout

namespace ProofFarm.CRT

-- ============================================================
-- MOD OF PRODUCTS
-- ============================================================

/-- Reducing mod a product then mod a factor is the same as reducing mod the factor. -/
-- ENGLISH: If you take remainder by m*n, then take remainder by m, you get the same as just taking remainder by m.
theorem mod_mul_mod_left (a m n : Nat) (hm : 0 < m) : (a % (m * n)) % m = a % m := by
  --PROOF_START[mod_mul_mod_left]
  rw [Nat.mod_mod_of_dvd]
  exact ⟨n, rfl⟩
  --PROOF_END[mod_mul_mod_left]

/-- Same for the right factor. -/
-- ENGLISH: If you take remainder by m*n, then take remainder by n, you get the same as just taking remainder by n.
theorem mod_mul_mod_right (a m n : Nat) (hn : 0 < n) : (a % (m * n)) % n = a % n := by
  --PROOF_START[mod_mul_mod_right]
  rw [Nat.mod_mod_of_dvd]
  exact ⟨m, by rw [Nat.mul_comm]⟩
  --PROOF_END[mod_mul_mod_right]

/-- A multiple of m has remainder 0 mod m. -/
-- ENGLISH: Any multiple of m is divisible by m (remainder is 0).
theorem mul_mod_zero (k m : Nat) : (k * m) % m = 0 := by
  --PROOF_START[mul_mod_zero]
  rw [Nat.mul_comm]; exact Nat.mul_mod_right m k
  --PROOF_END[mul_mod_zero]

/-- Mod preserves addition structure. -/
-- ENGLISH: (a + b) mod n = ((a mod n) + b) mod n. You can partially reduce before adding.
theorem add_mod_left (a b n : Nat) : (a + b) % n = ((a % n) + b) % n := by
  --PROOF_START[add_mod_left]
  rw [Nat.add_mod a b n, Nat.add_mod (a % n) b n, Nat.mod_mod]
  --PROOF_END[add_mod_left]

-- ============================================================
-- HELPERS for mod ↔ dvd
-- ============================================================

/-- If a ≡ b (mod m) and a ≥ b, then m ∣ (a - b). -/
private theorem dvd_sub_of_mod_eq (a b m : Nat) (hab : a ≥ b) (hmod : a % m = b % m) (hm : 0 < m) : m ∣ (a - b) := by
  have h1 : a = b + (a - b) := by omega
  have h2 : (b + (a - b)) % m = b % m := by rw [← h1]; exact hmod
  rw [Nat.add_mod] at h2
  have hr : b % m < m := Nat.mod_lt _ hm
  have hs : (a - b) % m < m := Nat.mod_lt _ hm
  have h3 : (a - b) % m = 0 := by
    if hlt : b % m + (a - b) % m < m then
      rw [Nat.mod_eq_of_lt hlt] at h2; omega
    else
      exfalso
      have hdiv := Nat.div_add_mod (b % m + (a - b) % m) m
      rw [h2] at hdiv
      have heq : m * ((b % m + (a - b) % m) / m) = (a - b) % m := by omega
      have hq : (b % m + (a - b) % m) / m ≥ 1 := Nat.div_pos (by omega) hm
      have : (a - b) % m ≥ m := by
        calc (a - b) % m = m * ((b % m + (a - b) % m) / m) := by omega
        _ ≥ m * 1 := Nat.mul_le_mul_left m hq
        _ = m := Nat.mul_one m
      omega
  exact Nat.dvd_of_mod_eq_zero h3

/-- If d ∣ (a - b) and a ≥ b, then a % d = b % d. -/
private theorem mod_eq_of_dvd_sub (a b d : Nat) (hab : a ≥ b) (hdvd : d ∣ (a - b)) : a % d = b % d := by
  obtain ⟨k, hk⟩ := hdvd
  have : a = b + d * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

-- ============================================================
-- COPRIME PRODUCT DIVISIBILITY
-- ============================================================

/-- If coprime m, n both divide x, then m*n divides x. -/
-- ENGLISH: If two coprime numbers each divide x, then their product divides x. This is the key to CRT uniqueness.
theorem coprime_mul_dvd_of_dvd (m n x : Nat) (hc : GCD.Coprime m n) (hm : m ∣ x) (hn : n ∣ x) :
    m * n ∣ x := by
  --PROOF_START[coprime_mul_dvd_of_dvd]
  exact GCD.coprime_mul_dvd m n x hc hm hn
  --PROOF_END[coprime_mul_dvd_of_dvd]

/-- If a ≡ b mod m and a ≡ b mod n and gcd(m,n)=1, then a ≡ b mod (m*n). -/
-- ENGLISH: If two numbers agree modulo m and modulo n (where m,n are coprime), they agree modulo m*n.
theorem coprime_mod_eq (a b m n : Nat) (hc : GCD.Coprime m n)
    (hm : a % m = b % m) (hn : a % n = b % n) : a % (m * n) = b % (m * n) := by
  --PROOF_START[coprime_mod_eq]
  -- Handle m = 0 or n = 0 edge cases
  if hm0 : m = 0 then
    simp [hm0]
    rw [hm0] at hm; simp at hm; rw [hm]
  else if hn0 : n = 0 then
    simp [hn0]
    rw [hn0] at hn; simp at hn; rw [hn]
  else
    have hmp : 0 < m := by omega
    have hnp : 0 < n := by omega
    if hab : a ≥ b then
      -- m | (a - b) and n | (a - b)
      have hm_dvd : m ∣ (a - b) := dvd_sub_of_mod_eq a b m hab hm hmp
      have hn_dvd : n ∣ (a - b) := dvd_sub_of_mod_eq a b n hab hn hnp
      have hmn_dvd : m * n ∣ (a - b) := coprime_mul_dvd_of_dvd m n (a - b) hc hm_dvd hn_dvd
      exact mod_eq_of_dvd_sub a b (m * n) hab hmn_dvd
    else
      -- b > a: symmetric
      have hba : b ≥ a := by omega
      have hm_dvd : m ∣ (b - a) := dvd_sub_of_mod_eq b a m hba hm.symm hmp
      have hn_dvd : n ∣ (b - a) := dvd_sub_of_mod_eq b a n hba hn.symm hnp
      have hmn_dvd : m * n ∣ (b - a) := coprime_mul_dvd_of_dvd m n (b - a) hc hm_dvd hn_dvd
      exact (mod_eq_of_dvd_sub b a (m * n) hba hmn_dvd).symm
  --PROOF_END[coprime_mod_eq]

-- ============================================================
-- CHINESE REMAINDER THEOREM
-- ============================================================

/-- CRT existence: given coprime m, n and target remainders, a solution exists. -/
-- ENGLISH: If m and n share no common factor, you can find a number with any desired remainders mod m and mod n simultaneously. This is the Chinese Remainder Theorem, discovered by Sun Zi around 250 AD.
theorem crt_existence (m n r1 r2 : Nat) (hm : 1 < m) (hn : 1 < n)
    (hc : GCD.Coprime m n) (hr1 : r1 < m) (hr2 : r2 < n) :
    ∃ x : Nat, x < m * n ∧ x % m = r1 ∧ x % n = r2 := by
  --PROOF_START[crt_existence]
  -- Need GCD.Coprime n m for Bezout direction
  have hcnm : GCD.Coprime n m := GCD.coprime_comm m n hc
  -- Find inverse of n mod m: ∃ n_inv < m, (n * n_inv) % m = 1
  have ⟨n_inv, hn_inv_lt, hn_inv_eq⟩ := Bezout.mod_inverse_exists n m hm hcnm
  -- Find inverse of m mod n: ∃ m_inv < n, (m * m_inv) % n = 1
  have hcmn : GCD.Coprime m n := hc
  have ⟨m_inv, hm_inv_lt, hm_inv_eq⟩ := Bezout.mod_inverse_exists m n hn hcmn
  -- Construct x = (r1 * n * n_inv + r2 * m * m_inv) % (m * n)
  let x := (r1 * n * n_inv + r2 * m * m_inv) % (m * n)
  have hmn_pos : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  refine ⟨x, ?_, ?_, ?_⟩
  · -- x < m * n
    exact Nat.mod_lt _ hmn_pos
  · -- x % m = r1
    -- x = (r1 * n * n_inv + r2 * m * m_inv) % (m * n)
    -- x % m = ((r1 * n * n_inv + r2 * m * m_inv) % (m * n)) % m
    --       = (r1 * n * n_inv + r2 * m * m_inv) % m  (by mod_mul_mod_left)
    --       = (r1 * n * n_inv + 0) % m  (since (r2 * m * m_inv) % m = 0)
    --       = (r1 * n * n_inv) % m
    --       = (r1 * (n * n_inv)) % m
    --       = (r1 * (n * n_inv % m)) % m ... etc
    show ((r1 * n * n_inv + r2 * m * m_inv) % (m * n)) % m = r1
    rw [mod_mul_mod_left _ m n (by omega)]
    -- Goal: (r1 * n * n_inv + r2 * m * m_inv) % m = r1
    -- r2 * m * m_inv = (r2 * m_inv) * m, so this is 0 mod m
    have h1 : (r2 * m * m_inv) % m = 0 := by
      rw [show r2 * m * m_inv = r2 * m_inv * m from by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      exact mul_mod_zero (r2 * m_inv) m
    -- (r1 * n * n_inv + r2 * m * m_inv) % m = (r1 * n * n_inv % m + 0) % m
    rw [Nat.add_mod, h1, Nat.add_zero, Nat.mod_mod]
    -- Goal: (r1 * n * n_inv) % m = r1
    -- (r1 * n * n_inv) % m = (r1 * (n * n_inv)) % m
    rw [Nat.mul_assoc]
    -- = (r1 * (n * n_inv % m)) % m ... we know n * n_inv % m = 1
    rw [Nat.mul_mod r1 (n * n_inv) m, hn_inv_eq, Nat.mul_one, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hr1
  · -- x % n = r2 (symmetric)
    show ((r1 * n * n_inv + r2 * m * m_inv) % (m * n)) % n = r2
    rw [mod_mul_mod_right _ m n (by omega)]
    have h1 : (r1 * n * n_inv) % n = 0 := by
      rw [show r1 * n * n_inv = r1 * n_inv * n from by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      exact mul_mod_zero (r1 * n_inv) n
    rw [Nat.add_mod, h1, Nat.zero_add, Nat.mod_mod]
    rw [Nat.mul_assoc]
    rw [Nat.mul_mod r2 (m * m_inv) n, hm_inv_eq, Nat.mul_one, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hr2
  --PROOF_END[crt_existence]

/-- CRT uniqueness: the solution is unique modulo m*n. -/
-- ENGLISH: The CRT solution is the ONLY number less than m*n with those remainders.
theorem crt_uniqueness (m n x y : Nat) (hm : 0 < m) (hn : 0 < n)
    (hc : GCD.Coprime m n)
    (hxm : x % m = y % m) (hxn : x % n = y % n) : x % (m * n) = y % (m * n) := by
  --PROOF_START[crt_uniqueness]
  exact coprime_mod_eq x y m n hc hxm hxn
  --PROOF_END[crt_uniqueness]

/-- CRT injection: the map x -> (x % m, x % n) is injective on {0, ..., m*n - 1}. -/
-- ENGLISH: Two numbers less than m*n that agree mod m and mod n must be equal.
theorem crt_injective (m n x y : Nat) (hm : 0 < m) (hn : 0 < n)
    (hc : GCD.Coprime m n)
    (hx : x < m * n) (hy : y < m * n)
    (hxm : x % m = y % m) (hxn : x % n = y % n) : x = y := by
  --PROOF_START[crt_injective]
  have h := crt_uniqueness m n x y hm hn hc hxm hxn
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact h
  --PROOF_END[crt_injective]

-- ============================================================
-- CRT COROLLARIES
-- ============================================================

/-- CRT for congruences: if a ≡ b mod p and a ≡ b mod q with p,q coprime, then a ≡ b mod p*q. -/
-- ENGLISH: Matching remainders mod two coprime numbers means matching remainder mod their product. This is the form used in RSA.
theorem crt_combine (a b p q : Nat) (hc : GCD.Coprime p q)
    (hp : a % p = b % p) (hq : a % q = b % q) : a % (p * q) = b % (p * q) := by
  --PROOF_START[crt_combine]
  exact coprime_mod_eq a b p q hc hp hq
  --PROOF_END[crt_combine]

/-- Product of two primes: distinct primes are coprime. -/
-- ENGLISH: Two different prime numbers always share no common factor.
theorem primes_coprime (p q : Nat) (hp : Primes.IsPrime p) (hq : Primes.IsPrime q) (hne : p ≠ q) :
    GCD.Coprime p q := by
  --PROOF_START[primes_coprime]
  unfold GCD.Coprime
  rw [GCD.gcd_eq_nat_gcd]
  have hg := Nat.gcd_dvd_left p q
  have hg2 := Nat.gcd_dvd_right p q
  cases hp.2 (Nat.gcd p q) hg with
  | inl h => exact h
  | inr h =>
    rw [h] at hg2
    cases hq.2 p hg2 with
    | inl h2 => have := hp.1; omega
    | inr h2 => exact absurd h2 hne
  --PROOF_END[primes_coprime]

/-- The product of two primes greater than 1. -/
-- ENGLISH: The product of two primes is at least 4.
theorem prime_mul_pos (p q : Nat) (hp : Primes.IsPrime p) (hq : Primes.IsPrime q) :
    0 < p * q := by
  --PROOF_START[prime_mul_pos]
  have hp2 := hp.1
  have hq2 := hq.1
  exact Nat.mul_pos (by omega) (by omega)
  --PROOF_END[prime_mul_pos]

end ProofFarm.CRT
