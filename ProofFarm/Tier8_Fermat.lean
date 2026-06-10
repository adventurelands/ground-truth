/-
  ProofFarm.Tier8_Fermat
  Power properties and Fermat's Little Theorem.
  The capstone of the proof chain.
-/
import ProofFarm.Tier7_Primes

namespace ProofFarm.Fermat

-- ============================================================
-- POWER BASICS
-- ============================================================

/-- Anything to the power 0 is 1. -/
-- ENGLISH: Any number raised to the zeroth power is 1.
theorem pow_zero (a : Nat) : a ^ 0 = 1 := by
  --PROOF_START[pow_zero]
  rfl
  --PROOF_END[pow_zero]

/-- Anything to the power 1 is itself. -/
-- ENGLISH: Any number raised to the first power is itself.
theorem pow_one (a : Nat) : a ^ 1 = a := by
  --PROOF_START[pow_one]
  simp
  --PROOF_END[pow_one]

/-- Power addition law. -/
-- ENGLISH: a^(m+n) = a^m * a^n. Multiplying powers means adding exponents.
theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  --PROOF_START[pow_add]
  exact Nat.pow_add a m n
  --PROOF_END[pow_add]

/-- Power multiplication law. -/
-- ENGLISH: (a^m)^n = a^(m*n). A power of a power means multiplying exponents.
theorem pow_mul (a m n : Nat) : (a ^ m) ^ n = a ^ (m * n) := by
  --PROOF_START[pow_mul]
  exact (Nat.pow_mul a m n).symm
  --PROOF_END[pow_mul]

/-- One to any power is one. -/
-- ENGLISH: 1 raised to any power is still 1.
theorem one_pow (n : Nat) : 1 ^ n = 1 := by
  --PROOF_START[one_pow]
  exact Nat.one_pow n
  --PROOF_END[one_pow]

/-- Zero to any positive power is zero. -/
-- ENGLISH: 0 raised to any positive power is 0.
theorem zero_pow (n : Nat) (hn : 0 < n) : 0 ^ n = 0 := by
  --PROOF_START[zero_pow]
  cases n with | zero => omega | succ n => simp [Nat.pow_succ]
  --PROOF_END[zero_pow]

/-- Powers preserve positivity. -/
-- ENGLISH: If a > 0, then a^n > 0 for all n.
theorem pow_pos (a n : Nat) (ha : 0 < a) : 0 < a ^ n := by
  --PROOF_START[pow_pos]
  exact Nat.pos_of_ne_zero (by
    induction n with
    | zero => simp
    | succ n ih => simp [Nat.pow_succ]; exact Nat.mul_ne_zero ih (by omega))
  --PROOF_END[pow_pos]

-- ============================================================
-- MODULAR EXPONENTIATION
-- ============================================================

/-- Mod distributes into powers. -/
-- ENGLISH: (a^n) mod m = ((a mod m)^n) mod m. You can reduce the base before exponentiating.
theorem pow_mod (a n m : Nat) : (a ^ n) % m = ((a % m) ^ n) % m := by
  --PROOF_START[pow_mod]
  exact Nat.pow_mod a n m
  --PROOF_END[pow_mod]

/-- a^2 mod p = (a mod p)^2 mod p. -/
-- ENGLISH: Squaring mod p is the same as reducing first then squaring.
theorem sq_mod (a p : Nat) : (a * a) % p = ((a % p) * (a % p)) % p := by
  --PROOF_START[sq_mod]
  exact Nat.mul_mod a a p
  --PROOF_END[sq_mod]

-- ============================================================
-- TOWARD FERMAT'S LITTLE THEOREM
-- ============================================================

/-- Multiplying both sides of a mod equation preserves the congruence. -/
-- ENGLISH: If a ≡ b (mod m), then a*c ≡ b*c (mod m). Multiplication respects modular equivalence.
theorem mul_mod_congr (a b c m : Nat) (h : a % m = b % m) : (a * c) % m = (b * c) % m := by
  --PROOF_START[mul_mod_congr]
  calc (a * c) % m = ((a % m) * (c % m)) % m := Nat.mul_mod a c m
  _ = ((b % m) * (c % m)) % m := by rw [h]
  _ = (b * c) % m := (Nat.mul_mod b c m).symm
  --PROOF_END[mul_mod_congr]

/-- Powers preserve modular congruence. -/
-- ENGLISH: If a ≡ b (mod m), then a^n ≡ b^n (mod m). You can raise both sides of a congruence to a power.
theorem pow_mod_congr (a b n m : Nat) (h : a % m = b % m) : (a ^ n) % m = (b ^ n) % m := by
  --PROOF_START[pow_mod_congr]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.pow_succ]
    calc (a ^ n * a) % m = ((a ^ n % m) * (a % m)) % m := Nat.mul_mod _ _ _
    _ = ((b ^ n % m) * (b % m)) % m := by rw [ih, h]
    _ = (b ^ n * b) % m := (Nat.mul_mod _ _ _).symm
  --PROOF_END[pow_mod_congr]

/-- Successive powers differ by a factor. -/
-- ENGLISH: a^(n+1) = a * a^n. Each successive power is just one more multiplication.
theorem pow_succ' (a n : Nat) : a ^ (n + 1) = a * a ^ n := by
  --PROOF_START[pow_succ']
  rw [Nat.pow_succ, Nat.mul_comm]
  --PROOF_END[pow_succ']

-- ============================================================
-- BINOMIAL COEFFICIENT INFRASTRUCTURE FOR FERMAT'S LITTLE THEOREM
-- ============================================================

/-- Binomial coefficients via Pascal's triangle. -/
def C : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => C n k + C n (k + 1)

/-- Factorial function. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- C n k = 0 when n < k. -/
theorem C_gt (n k : Nat) (h : n < k) : C n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ k => rfl
  | succ n ih => cases k with | zero => omega | succ k =>
    have := ih k (by omega); have := ih (k+1) (by omega); show C n k + C n (k+1) = 0; omega

/-- The key identity: C(n,k) * k! * (n-k)! = n! -/
theorem C_factorial (n k : Nat) (hk : k ≤ n) :
    C n k * factorial k * factorial (n - k) = factorial n := by
  induction n generalizing k with
  | zero => cases k with | zero => simp [C, factorial] | succ k => omega
  | succ n ih =>
    cases k with
    | zero => simp [C, factorial]
    | succ k =>
      have hk' : k ≤ n := by omega
      calc C (n+1) (k+1) * factorial (k+1) * factorial (n+1 - (k+1))
          = (C n k + C n (k+1)) * factorial (k+1) * factorial (n - k) := by simp [C, Nat.succ_sub_succ]
        _ = C n k * factorial (k+1) * factorial (n-k) + C n (k+1) * factorial (k+1) * factorial (n-k) := by rw [Nat.add_mul, Nat.add_mul]
        _ = (k+1) * factorial n + C n (k+1) * factorial (k+1) * factorial (n-k) := by
            congr 1; show C n k * ((k+1) * factorial k) * factorial (n - k) = (k+1) * factorial n
            have : C n k * ((k+1) * factorial k) * factorial (n-k) = (k+1) * (C n k * factorial k * factorial (n-k)) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            rw [this, ih k hk']
        _ = (k+1) * factorial n + (n-k) * factorial n := by
            congr 1; rcases Nat.lt_or_eq_of_le hk' with hlt | heq
            · have fac_eq : factorial (n-k) = (n-k) * factorial (n-k-1) := by
                match h : n - k with | 0 => omega | m+1 => rfl
              rw [fac_eq]
              have : C n (k+1) * factorial (k+1) * ((n-k) * factorial (n-k-1)) =
                    (n-k) * (C n (k+1) * factorial (k+1) * factorial (n-k-1)) := by
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              rw [this]; congr 1
              have : n - k - 1 = n - (k+1) := by omega
              rw [this]; exact ih (k+1) (by omega)
            · subst heq; simp [C_gt k (k+1) (by omega)]
        _ = (n+1) * factorial n := by rw [← Nat.add_mul]; congr 1; omega
        _ = factorial (n+1) := rfl

/-- A prime doesn't divide m! for m < p. -/
theorem prime_not_dvd_factorial (p m : Nat) (hp : Primes.IsPrime p) (hm : m < p) :
    ¬(p ∣ factorial m) := by
  induction m with
  | zero =>
    show ¬(p ∣ 1)
    intro h; have := Nat.le_of_dvd Nat.one_pos h; have := hp.1; omega
  | succ m ih =>
    show ¬(p ∣ (m + 1) * factorial m)
    intro hdvd
    cases Primes.prime_dvd_mul p (m + 1) (factorial m) hp hdvd with
    | inl h => have := Nat.le_of_dvd (by omega) h; have := hp.1; omega
    | inr h => exact ih (by omega) h

/-- p divides C(p,k) for 0 < k < p when p is prime. -/
theorem prime_dvd_C (p k : Nat) (hp : Primes.IsPrime p) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ C p k := by
  have hcf := C_factorial p k (by omega)
  have hfp : factorial p = p * factorial (p - 1) := by
    cases p with | zero => have := hp.1; omega | succ n => rfl
  have hdvd : p ∣ C p k * factorial k * factorial (p - k) := by
    rw [hcf, hfp]; exact ⟨factorial (p - 1), rfl⟩
  have hp2 := hp.1
  have hpk := prime_not_dvd_factorial p k hp hkp
  have hppk := prime_not_dvd_factorial p (p - k) hp (by omega)
  cases Primes.prime_dvd_mul p (C p k * factorial k) (factorial (p - k)) hp hdvd with
  | inl h => cases Primes.prime_dvd_mul p (C p k) (factorial k) hp h with
    | inl h => exact h
    | inr h => exact absurd h hpk
  | inr h => exact absurd h hppk

-- ============================================================
-- BINOMIAL SUM AND THEOREM MACHINERY
-- ============================================================

/-- binomSum a n j = sum_{k=0}^{j} C(n,k) * a^k -/
def binomSum (a n : Nat) : Nat → Nat
  | 0 => 1  -- C(n,0) * a^0 = 1
  | j + 1 => binomSum a n j + C n (j + 1) * a ^ (j + 1)

/-- C n n = 1 for all n. -/
theorem C_self (n : Nat) : C n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => show C n n + C n (n + 1) = 1; rw [ih, C_gt n (n + 1) (by omega)]

/-- binomSum with j > n adds nothing (since C(n,k)=0 for k>n). -/
theorem binomSum_succ_of_ge (a n j : Nat) (hj : n ≤ j) :
    binomSum a n (j + 1) = binomSum a n j := by
  show binomSum a n j + C n (j + 1) * a ^ (j + 1) = binomSum a n j
  rw [C_gt n (j + 1) (by omega)]; simp

/-- binomSum past n gives the same as at n. -/
theorem binomSum_past (a n j : Nat) (hj : n ≤ j) : binomSum a n j = binomSum a n n := by
  induction j with
  | zero => cases n with | zero => rfl | succ n => omega
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hj with h | h
    · rw [binomSum_succ_of_ge a n j (by omega)]
      exact ih (by omega)
    · cases h; rfl

/-- Key Pascal recursion for binomSum:
    binomSum a (n+1) (j+1) = binomSum a n (j+1) + a * binomSum a n j -/
theorem binomSum_pascal (a n j : Nat) :
    binomSum a (n + 1) (j + 1) = binomSum a n (j + 1) + a * binomSum a n j := by
  induction j with
  | zero =>
    show 1 + C (n+1) 1 * a ^ 1 = (1 + C n 1 * a ^ 1) + a * 1
    simp
    -- Goal: 1 + C (n+1) 1 * a = 1 + C n 1 * a + a
    -- C(n+1, 1) = C n 0 + C n 1 = 1 + C n 1
    show 1 + (C n 0 + C n 1) * a = 1 + C n 1 * a + a
    simp [C, Nat.add_mul]
    omega
  | succ j ih =>
    -- LHS = binomSum a (n+1) (j+2)
    --      = binomSum a (n+1) (j+1) + C(n+1, j+2) * a^(j+2)
    -- By IH: binomSum a (n+1) (j+1) = binomSum a n (j+1) + a * binomSum a n j
    -- C(n+1, j+2) = C(n, j+1) + C(n, j+2)   (Pascal)
    -- RHS = binomSum a n (j+2) + a * binomSum a n (j+1)
    --     = (binomSum a n (j+1) + C(n,j+2)*a^(j+2)) + a*(binomSum a n j + C(n,j+1)*a^(j+1))
    --     = binomSum a n (j+1) + C(n,j+2)*a^(j+2) + a*binomSum a n j + C(n,j+1)*a^(j+2)
    --     = (binomSum a n (j+1) + a*binomSum a n j) + (C(n,j+1) + C(n,j+2))*a^(j+2)
    --     = binomSum a (n+1) (j+1) + C(n+1, j+2)*a^(j+2)   (by IH and Pascal)
    --     = LHS ✓
    show binomSum a (n+1) (j+1) + C (n+1) (j+2) * a^(j+2)
       = (binomSum a n (j+1) + C n (j+2) * a^(j+2)) + a * (binomSum a n j + C n (j+1) * a^(j+1))
    rw [ih]
    -- Now LHS = (binomSum a n (j+1) + a * binomSum a n j) + C(n+1,j+2) * a^(j+2)
    -- RHS = binomSum a n (j+1) + C(n,j+2)*a^(j+2) + a*binomSum a n j + a*(C(n,j+1)*a^(j+1))
    -- Need: C(n+1,j+2) * a^(j+2) = C(n,j+2)*a^(j+2) + a*C(n,j+1)*a^(j+1)
    -- i.e. C(n+1,j+2) * a^(j+2) = C(n,j+2)*a^(j+2) + C(n,j+1)*a^(j+2)
    -- i.e. C(n+1,j+2) = C(n,j+1) + C(n,j+2)  -- Pascal! ✓
    -- And a * (C(n,j+1) * a^(j+1)) = C(n,j+1) * a^(j+2)
    have ha_pow : a * (C n (j+1) * a^(j+1)) = C n (j+1) * a^(j+2) := by
      have : a ^ (j + 2) = a * a ^ (j + 1) := by rw [pow_succ']
      rw [this]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [Nat.mul_add, ha_pow]
    -- Now both sides should match after rearranging
    -- LHS: binomSum a n (j+1) + a * binomSum a n j + C(n+1,j+2) * a^(j+2)
    -- RHS: binomSum a n (j+1) + C(n,j+2)*a^(j+2) + a*binomSum a n j + C(n,j+1)*a^(j+2)
    -- Need: C(n+1,j+2) = C(n,j+1) + C(n,j+2)
    show binomSum a n (j + 1) + a * binomSum a n j + (C n (j + 1) + C n (j + 2)) * a ^ (j + 2)
       = binomSum a n (j + 1) + C n (j + 2) * a ^ (j + 2) + (a * binomSum a n j + C n (j + 1) * a ^ (j + 2))
    rw [Nat.add_mul]
    omega

/-- (1+a) * binomSum a n n = binomSum a (n+1) (n+1) -/
theorem binomSum_step (a n : Nat) :
    binomSum a n n + a * binomSum a n n = binomSum a (n + 1) (n + 1) := by
  have h := binomSum_pascal a n n
  -- h : binomSum a (n+1) (n+1) = binomSum a n (n+1) + a * binomSum a n n
  rw [binomSum_succ_of_ge a n n (Nat.le_refl n)] at h
  exact h.symm

/-- Binomial theorem: (a+1)^n = binomSum a n n -/
theorem binomial_thm (a n : Nat) : (a + 1) ^ n = binomSum a n n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    -- (a+1)^(n+1) = (a+1) * (a+1)^n = (a+1) * binomSum a n n
    rw [ih]
    -- Need: (a + 1) * binomSum a n n = binomSum a (n+1) (n+1)
    show (a + 1) * binomSum a n n = binomSum a (n + 1) (n + 1)
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    exact binomSum_step a n

/-- The middle terms of binomSum (k=1..p-1) are divisible by p. -/
theorem binomSum_mod_p (a p j : Nat) (hp : Primes.IsPrime p) (hj : j < p) :
    binomSum a p j % p = 1 % p := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (binomSum a p j + C p (j+1) * a^(j+1)) % p = 1 % p
    have hdvd : p ∣ C p (j+1) * a^(j+1) := by
      have hc := prime_dvd_C p (j+1) hp (by omega) hj
      obtain ⟨c, hc⟩ := hc
      exact ⟨c * a^(j+1), by rw [hc]; simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    calc (binomSum a p j + p * c) % p
        = (binomSum a p j % p + (p * c) % p) % p := Nat.add_mod _ _ _
      _ = (binomSum a p j % p + 0) % p := by rw [Nat.mul_mod_right]
      _ = binomSum a p j % p := by simp
      _ = 1 % p := ih (by omega)

/-- binomSum a p p = binomSum a p (p-1) + a^p when p ≥ 1 -/
theorem binomSum_last (a p : Nat) (hp : 1 ≤ p) :
    binomSum a p p = binomSum a p (p - 1) + a ^ p := by
  cases p with
  | zero => omega
  | succ n =>
    show binomSum a (n+1) n + C (n+1) (n+1) * a^(n+1) = binomSum a (n+1) n + a^(n+1)
    rw [C_self]; simp

/-- Freshman's dream: (a+1)^p ≡ a^p + 1 (mod p) when p is prime. -/
theorem freshman_dream (a p : Nat) (hp : Primes.IsPrime p) :
    (a + 1) ^ p % p = (a ^ p + 1) % p := by
  rw [binomial_thm, binomSum_last a p (by have := hp.1; omega)]
  have hp2 : 1 ≤ p := by have := hp.1; omega
  -- binomSum a p (p-1) + a^p
  -- binomSum a p (p-1) ≡ 1 (mod p)
  have hmod := binomSum_mod_p a p (p - 1) hp (by omega)
  calc (binomSum a p (p - 1) + a ^ p) % p
      = (binomSum a p (p - 1) % p + a ^ p % p) % p := Nat.add_mod _ _ _
    _ = (1 % p + a ^ p % p) % p := by rw [hmod]
    _ = (a ^ p % p + 1 % p) % p := by rw [Nat.add_comm]
    _ = (a ^ p + 1) % p := (Nat.add_mod _ _ _).symm

/-- Fermat's Little Theorem (additive form): a^p ≡ a (mod p). -/
-- ENGLISH: If p is prime, then a^p mod p = a mod p for any a. This is Fermat's Little Theorem, one of the most important results in number theory.
theorem fermat_little (a p : Nat) (hp : Primes.IsPrime p) : a ^ p % p = a % p := by
  --PROOF_START[fermat_little]
  induction a with
  | zero =>
    -- 0^p % p = 0 % p. Since p ≥ 2, 0^p = 0.
    have hp1 : 0 < p := by have := hp.1; omega
    rw [zero_pow p hp1]
  | succ a ih =>
    -- (a+1)^p % p = (a^p + 1) % p  (freshman's dream)
    -- = (a % p + 1) % p             (by IH: a^p % p = a % p)
    -- = (a + 1) % p                 (mod arithmetic)
    calc (a + 1) ^ p % p
        = (a ^ p + 1) % p := freshman_dream a p hp
      _ = (a ^ p % p + 1 % p) % p := Nat.add_mod _ _ _
      _ = (a % p + 1 % p) % p := by rw [ih]
      _ = (a + 1) % p := (Nat.add_mod _ _ _).symm
  --PROOF_END[fermat_little]

/-- Fermat's Little Theorem (multiplicative form): a^(p-1) ≡ 1 (mod p) when gcd(a,p) = 1. -/
-- ENGLISH: If p is prime and a is not divisible by p, then a^(p-1) mod p = 1. This is the version used in RSA encryption.
theorem fermat_little_mul (a p : Nat) (hp : Primes.IsPrime p) (ha : ¬(p ∣ a)) : a ^ (p - 1) % p = 1 := by
  --PROOF_START[fermat_little_mul]
  -- a ≥ 1 since p ∣ 0 but ¬(p ∣ a)
  have ha1 : a ≥ 1 := by
    cases a with | zero => exact absurd ⟨0, by omega⟩ ha | succ n => omega
  have hp2 := hp.1  -- p ≥ 2
  -- a^p = a * a^(p-1)
  have hap : a ^ p = a * a ^ (p - 1) := by
    cases p with
    | zero => omega
    | succ n => exact pow_succ' a n
  -- From FLT: a^p % p = a % p
  have hflt := fermat_little a p hp
  -- We need: a^(p-1) ≥ 1
  have hap1 : a ^ (p - 1) ≥ 1 := Nat.one_le_pow _ _ ha1
  -- a^p ≥ a (since a^(p-1) ≥ 1 and a ≥ 1)
  have hge : a ^ p ≥ a := by
    rw [hap]; exact Nat.le_mul_of_pos_right a (by omega)
  -- p ∣ (a^p - a): from a^p % p = a % p
  -- (a^p - a) % p = 0
  have hdvd_diff : p ∣ (a ^ p - a) := by
    have : (a ^ p - a) % p = 0 := by
      -- a % p = (a + (a^p - a)) % p = (a % p + (a^p - a) % p) % p
      have h1 : a ^ p % p = (a + (a ^ p - a)) % p := by congr 1; omega
      rw [hflt] at h1
      have h3 : (a + (a ^ p - a)) % p = (a % p + (a ^ p - a) % p) % p := Nat.add_mod _ _ _
      rw [h3] at h1
      -- a % p = (a % p + (a^p - a) % p) % p
      -- Let r = a % p, s = (a^p - a) % p
      -- r = (r + s) % p
      -- Since r < p and s < p: if r + s < p then r = r + s so s = 0
      -- if r + s ≥ p then r = r + s - p so s = p ... but s < p, contradiction
      have hr : a % p < p := Nat.mod_lt _ (by omega)
      have hs : (a ^ p - a) % p < p := Nat.mod_lt _ (by omega)
      by_cases hsz : (a ^ p - a) % p = 0
      · exact hsz
      · exfalso
        have hs_pos : 0 < (a ^ p - a) % p := by omega
        -- (a % p + (a^p - a) % p) % p = a % p
        -- If a%p + s < p, then (a%p + s) % p = a%p + s, so a%p = a%p + s, so s = 0, contradiction
        -- If a%p + s ≥ p, then (a%p + s) % p = a%p + s - p, so a%p = a%p + s - p, so s = p, but s < p, contradiction
        by_cases hlt : a % p + (a ^ p - a) % p < p
        · rw [Nat.mod_eq_of_lt hlt] at h1; omega
        · have hge2 : a % p + (a ^ p - a) % p ≥ p := by omega
          have hlt2 : a % p + (a ^ p - a) % p < 2 * p := by omega
          have := Nat.mod_eq_sub_mod hge2
          rw [this] at h1
          have := Nat.mod_eq_of_lt (by omega : a % p + (a ^ p - a) % p - p < p)
          rw [this] at h1
          omega
    exact Nat.dvd_of_mod_eq_zero this
  -- a^p - a = a * (a^(p-1) - 1)
  have hfactor : a ^ p - a = a * (a ^ (p - 1) - 1) := by
    rw [hap]
    -- a * a^(p-1) - a = a * (a^(p-1) - 1)
    rw [Nat.mul_sub_one]
  -- Coprime p a
  have hcop : GCD.Coprime p a := Primes.coprime_of_prime_not_dvd p a hp ha
  -- p ∣ a * (a^(p-1) - 1)
  have hdvd2 : p ∣ a * (a ^ (p - 1) - 1) := by
    rw [← hfactor]; exact hdvd_diff
  -- By coprime_dvd_of_dvd_mul: p ∣ (a^(p-1) - 1)
  have hdvd3 : p ∣ (a ^ (p - 1) - 1) := GCD.coprime_dvd_of_dvd_mul p a (a ^ (p - 1) - 1) hcop hdvd2
  -- a^(p-1) = 1 + (a^(p-1) - 1)
  have hrewrite : a ^ (p - 1) = 1 + (a ^ (p - 1) - 1) := by omega
  rw [hrewrite]
  obtain ⟨c, hc⟩ := hdvd3
  rw [hc]
  calc (1 + p * c) % p
      = (1 % p + (p * c) % p) % p := Nat.add_mod _ _ _
    _ = (1 % p + 0) % p := by rw [Nat.mul_mod_right]
    _ = 1 % p := by simp
    _ = 1 := Nat.mod_eq_of_lt (by omega)
  --PROOF_END[fermat_little_mul]

end ProofFarm.Fermat
