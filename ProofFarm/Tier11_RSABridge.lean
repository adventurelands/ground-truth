/-
  ProofFarm.Tier11_RSABridge
  Connecting Fermat's Little Theorem to the RSA encryption setting.
  Key insight: case-split on whether p divides the message.
-/
import ProofFarm.Tier10_CRT

namespace ProofFarm.RSABridge

-- ============================================================
-- POWER HELPERS FOR RSA
-- ============================================================

/-- Raising a^(p-1) to power k: a^(k*(p-1)) mod p = 1 when p is prime and p does not divide a. -/
-- ENGLISH: If p is prime and doesn't divide a, then a raised to any multiple of (p-1) gives remainder 1 mod p. This generalizes Fermat's Little Theorem.
theorem fermat_pow_multiple (a p k : Nat) (hp : Primes.IsPrime p) (hnd : ¬(p ∣ a)) :
    a ^ (k * (p - 1)) % p = 1 := by
  --PROOF_START[fermat_pow_multiple]
  have hp2 : 2 ≤ p := Primes.prime_ge_two p hp
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  induction k with
  | zero => simp [hmod1]
  | succ n ih =>
    rw [Nat.succ_mul]
    rw [Nat.pow_add]
    rw [Nat.mul_mod]
    rw [ih]
    rw [Fermat.fermat_little_mul a p hp hnd]
    simp [hmod1]
  --PROOF_END[fermat_pow_multiple]

/-- If a^d ≡ 1 (mod m) and d divides e, then a^e ≡ 1 (mod m). -/
-- ENGLISH: If a power gives remainder 1, then any multiple of that power also gives remainder 1.
theorem pow_mod_one_of_dvd_exp (a d e m : Nat) (hd : d ∣ e) (h : a ^ d % m = 1) :
    a ^ e % m = 1 := by
  --PROOF_START[pow_mod_one_of_dvd_exp]
  obtain ⟨k, hk⟩ := hd
  subst hk
  have hm : m ≠ 1 := by
    intro hm1; rw [hm1] at h; omega
  have hmod1 : 1 % m = 1 := by
    cases m with
    | zero => simp
    | succ n => cases n with
      | zero => exact absurd rfl hm
      | succ n => exact Nat.mod_eq_of_lt (by omega)
  have : a ^ (d * k) = (a ^ d) ^ k := by rw [← Nat.pow_mul]
  rw [this]
  rw [Nat.pow_mod (a ^ d) k m]
  rw [h]
  rw [Fermat.one_pow k]
  exact hmod1
  --PROOF_END[pow_mod_one_of_dvd_exp]

/-- (p-1) divides (p-1)*(q-1). -/
-- ENGLISH: The product of two numbers is divisible by each factor. Trivial but needed.
theorem dvd_mul_right_sub (p q : Nat) : (p - 1) ∣ ((p - 1) * (q - 1)) := by
  --PROOF_START[dvd_mul_right_sub]
  exact ⟨q - 1, rfl⟩
  --PROOF_END[dvd_mul_right_sub]

/-- (q-1) divides (p-1)*(q-1). -/
-- ENGLISH: Same as above but for the other factor.
theorem dvd_mul_left_sub (p q : Nat) : (q - 1) ∣ ((p - 1) * (q - 1)) := by
  --PROOF_START[dvd_mul_left_sub]
  exact ⟨p - 1, Nat.mul_comm (p - 1) (q - 1)⟩
  --PROOF_END[dvd_mul_left_sub]

-- ============================================================
-- RSA CASES: COPRIME TO p
-- ============================================================

/-- RSA core for the coprime-to-p case: m^(d*e) ≡ m (mod p). -/
-- ENGLISH: When p doesn't divide the message, Fermat's theorem lets us reduce the exponent d*e. Since d*e ≡ 1 mod (p-1)*(q-1), the giant power simplifies to just m.
theorem rsa_case_coprime_p (m d e p q : Nat) (hp : Primes.IsPrime p)
    (hnd : ¬(p ∣ m)) (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1))) :
    m ^ (d * e) % p = m % p := by
  --PROOF_START[rsa_case_coprime_p]
  obtain ⟨k, hk⟩ := hde
  have hp2 : 2 ≤ p := Primes.prime_ge_two p hp
  rw [hk, Nat.pow_add, Nat.pow_one]
  have hfm : m ^ (k * ((p - 1) * (q - 1))) % p = 1 := by
    have : k * ((p - 1) * (q - 1)) = (k * (q - 1)) * (p - 1) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    rw [this]
    exact fermat_pow_multiple m p (k * (q - 1)) hp hnd
  calc (m * m ^ (k * ((p - 1) * (q - 1)))) % p
      = ((m % p) * (m ^ (k * ((p - 1) * (q - 1))) % p)) % p := Nat.mul_mod m _ p
    _ = ((m % p) * 1) % p := by rw [hfm]
    _ = (m % p) % p := by rw [Nat.mul_one]
    _ = m % p := Nat.mod_mod_of_dvd m ⟨1, by omega⟩
  --PROOF_END[rsa_case_coprime_p]

/-- Same for q. -/
-- ENGLISH: The symmetric case: when q doesn't divide the message.
theorem rsa_case_coprime_q (m d e p q : Nat) (hq : Primes.IsPrime q)
    (hnd : ¬(q ∣ m)) (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1))) :
    m ^ (d * e) % q = m % q := by
  --PROOF_START[rsa_case_coprime_q]
  obtain ⟨k, hk⟩ := hde
  have hq2 : 2 ≤ q := Primes.prime_ge_two q hq
  rw [hk, Nat.pow_add, Nat.pow_one]
  have hfm : m ^ (k * ((p - 1) * (q - 1))) % q = 1 := by
    have : k * ((p - 1) * (q - 1)) = (k * (p - 1)) * (q - 1) := by
      simp [Nat.mul_assoc]
    rw [this]
    exact fermat_pow_multiple m q (k * (p - 1)) hq hnd
  calc (m * m ^ (k * ((p - 1) * (q - 1)))) % q
      = ((m % q) * (m ^ (k * ((p - 1) * (q - 1))) % q)) % q := Nat.mul_mod m _ q
    _ = ((m % q) * 1) % q := by rw [hfm]
    _ = (m % q) % q := by rw [Nat.mul_one]
    _ = m % q := Nat.mod_mod_of_dvd m ⟨1, by omega⟩
  --PROOF_END[rsa_case_coprime_q]

-- ============================================================
-- RSA CASES: DIVISIBLE BY p
-- ============================================================

/-- If p divides m, then m^(d*e) ≡ 0 ≡ m (mod p). -/
-- ENGLISH: If the message is divisible by p, then any power of it is also divisible by p, so both sides are 0 mod p.
theorem rsa_case_zero_p (m d e p : Nat) (hp : Primes.IsPrime p) (hd : p ∣ m) (hde : 0 < d * e) :
    m ^ (d * e) % p = m % p := by
  --PROOF_START[rsa_case_zero_p]
  -- Both sides are 0 mod p since p | m
  have hpp : 0 < p := Primes.prime_pos p hp
  have hmp : m % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hpow : p ∣ m ^ (d * e) := by
    obtain ⟨n, hn⟩ : ∃ n, d * e = n + 1 := ⟨d * e - 1, by omega⟩
    rw [hn, Nat.pow_succ]
    exact Nat.dvd_trans hd ⟨m ^ n, by rw [Nat.mul_comm]⟩
  have hpowm : m ^ (d * e) % p = 0 := Nat.mod_eq_zero_of_dvd hpow
  rw [hpowm, hmp]
  --PROOF_END[rsa_case_zero_p]

/-- Same for q. -/
-- ENGLISH: Symmetric case for q.
theorem rsa_case_zero_q (m d e q : Nat) (hq : Primes.IsPrime q) (hd : q ∣ m) (hde : 0 < d * e) :
    m ^ (d * e) % q = m % q := by
  --PROOF_START[rsa_case_zero_q]
  have hqp : 0 < q := Primes.prime_pos q hq
  have hmq : m % q = 0 := Nat.mod_eq_zero_of_dvd hd
  have hpow : q ∣ m ^ (d * e) := by
    obtain ⟨n, hn⟩ : ∃ n, d * e = n + 1 := ⟨d * e - 1, by omega⟩
    rw [hn, Nat.pow_succ]
    exact Nat.dvd_trans hd ⟨m ^ n, by rw [Nat.mul_comm]⟩
  have hpowm : m ^ (d * e) % q = 0 := Nat.mod_eq_zero_of_dvd hpow
  rw [hpowm, hmq]
  --PROOF_END[rsa_case_zero_q]

-- ============================================================
-- RSA: UNCONDITIONAL MOD p AND MOD q
-- ============================================================

/-- m^(d*e) ≡ m (mod p), unconditionally. -/
-- ENGLISH: No matter what the message is, m^(d*e) and m have the same remainder mod p. This combines both cases (p divides m, and p doesn't divide m).
theorem rsa_mod_p (m d e p q : Nat) (hp : Primes.IsPrime p)
    (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1))) :
    m ^ (d * e) % p = m % p := by
  --PROOF_START[rsa_mod_p]
  by_cases hdvd : p ∣ m
  · have hpos : 0 < d * e := by
      obtain ⟨k, hk⟩ := hde; omega
    exact rsa_case_zero_p m d e p hp hdvd hpos
  · exact rsa_case_coprime_p m d e p q hp hdvd hde
  --PROOF_END[rsa_mod_p]

/-- m^(d*e) ≡ m (mod q), unconditionally. -/
-- ENGLISH: Same as above but for q.
theorem rsa_mod_q (m d e p q : Nat) (hq : Primes.IsPrime q)
    (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1))) :
    m ^ (d * e) % q = m % q := by
  --PROOF_START[rsa_mod_q]
  by_cases hdvd : q ∣ m
  · have hpos : 0 < d * e := by
      obtain ⟨k, hk⟩ := hde; omega
    exact rsa_case_zero_q m d e q hq hdvd hpos
  · exact rsa_case_coprime_q m d e p q hq hdvd hde
  --PROOF_END[rsa_mod_q]

end ProofFarm.RSABridge
