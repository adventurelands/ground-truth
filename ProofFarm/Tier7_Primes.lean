/-
  ProofFarm.Tier7_Primes
  Prime numbers, Euclid's lemma, and basic factorization.
-/
import ProofFarm.Tier6_GCD

namespace ProofFarm.Primes

-- ============================================================
-- PRIME DEFINITION
-- ============================================================

/-- A natural number is prime if it's ≥ 2 and its only divisors are 1 and itself. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- 2 is prime. -/
-- ENGLISH: 2 is the smallest prime number.
theorem two_is_prime : IsPrime 2 := by
  --PROOF_START[two_is_prime]
  constructor; · omega
  intro d hd; have := Nat.le_of_dvd (by omega) hd
  cases d with | zero => simp at hd | succ n =>
  cases n with | zero => left; rfl | succ m => right; omega
  --PROOF_END[two_is_prime]

/-- 3 is prime. -/
-- ENGLISH: 3 is a prime number.
theorem three_is_prime : IsPrime 3 := by
  --PROOF_START[three_is_prime]
  constructor; · omega
  intro d hd; have := Nat.le_of_dvd (by omega) hd; obtain ⟨k, hk⟩ := hd
  cases d with | zero => omega | succ n =>
  cases n with | zero => left; rfl | succ m =>
  cases m with | zero => exfalso; omega | succ l => right; omega
  --PROOF_END[three_is_prime]

/-- A prime is at least 2. -/
-- ENGLISH: Every prime number is 2 or bigger.
theorem prime_ge_two (p : Nat) (hp : IsPrime p) : 2 ≤ p := by
  --PROOF_START[prime_ge_two]
  exact hp.1
  --PROOF_END[prime_ge_two]

/-- A prime is positive. -/
-- ENGLISH: Every prime number is greater than zero.
theorem prime_pos (p : Nat) (hp : IsPrime p) : 0 < p := by
  --PROOF_START[prime_pos]
  have := hp.1; omega
  --PROOF_END[prime_pos]

/-- A prime is not one. -/
-- ENGLISH: 1 is not a prime number.
theorem prime_ne_one (p : Nat) (hp : IsPrime p) : p ≠ 1 := by
  --PROOF_START[prime_ne_one]
  have := hp.1; omega
  --PROOF_END[prime_ne_one]

-- ============================================================
-- EUCLID'S LEMMA
-- ============================================================

/-- A prime that doesn't divide a is coprime to a. -/
-- ENGLISH: If a prime p doesn't divide a, then gcd(p, a) = 1.
theorem coprime_of_prime_not_dvd (p a : Nat) (hp : IsPrime p) (hna : ¬(p ∣ a)) : GCD.Coprime p a := by
  --PROOF_START[coprime_of_prime_not_dvd]
  unfold GCD.Coprime
  cases hp.2 (GCD.gcd p a) (GCD.gcd_dvd_left p a) with
  | inl h => exact h
  | inr h => exfalso; have := GCD.gcd_dvd_right p a; rw [h] at this; exact hna this
  --PROOF_END[coprime_of_prime_not_dvd]

/-- If a prime divides a product, it divides one of the factors. -/
-- ENGLISH: If a prime divides a*b, then it must divide a or divide b. This is Euclid's lemma.
theorem prime_dvd_mul (p a b : Nat) (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  --PROOF_START[prime_dvd_mul]
  if ha : p ∣ a then left; exact ha
  else right; exact GCD.coprime_dvd_of_dvd_mul p a b (coprime_of_prime_not_dvd p a hp ha) h
  --PROOF_END[prime_dvd_mul]

-- ============================================================
-- EXISTENCE OF PRIME FACTORS
-- ============================================================

/-- Every number ≥ 2 has a prime divisor. -/
-- ENGLISH: Any number 2 or bigger is divisible by at least one prime.
theorem exists_prime_dvd (n : Nat) (hn : 2 ≤ n) : ∃ p, IsPrime p ∧ p ∣ n := by
  --PROOF_START[exists_prime_dvd]
  induction n using Nat.strongRecOn with
  | _ n ih =>
  -- Either n is prime or not
  by_cases hprime : IsPrime n
  · exact ⟨n, hprime, ⟨1, by omega⟩⟩
  · -- n is ≥ 2 but not prime, so the divisor condition fails
    -- IsPrime n = ⟨2 ≤ n, ∀ d, d ∣ n → d = 1 ∨ d = n⟩
    -- Since 2 ≤ n holds, ¬IsPrime n means ¬(∀ d, d ∣ n → d = 1 ∨ d = n)
    have hdivs : ¬(∀ d : Nat, d ∣ n → d = 1 ∨ d = n) := by
      intro hall; exact hprime ⟨hn, hall⟩
    -- Use Classical.choice to get a witness
    have ⟨d, hd⟩ := Classical.not_forall.mp hdivs
    have ⟨hd_dvd, hd_or⟩ := Classical.not_imp.mp hd
    have hd_ne1 : d ≠ 1 := fun h => hd_or (Or.inl h)
    have hd_ne_n : d ≠ n := fun h => hd_or (Or.inr h)
    have hd_pos : 0 < d := by
      cases d with
      | zero => obtain ⟨k, hk⟩ := hd_dvd; omega
      | succ d => omega
    have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hd_dvd
    have hd_lt : d < n := by omega
    have hd_ge2 : 2 ≤ d := by omega
    obtain ⟨p, hp, hp_dvd_d⟩ := ih d hd_lt hd_ge2
    exact ⟨p, hp, Nat.dvd_trans hp_dvd_d hd_dvd⟩
  --PROOF_END[exists_prime_dvd]

/-- Factorial function for the infinity-of-primes proof. -/
private def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

private theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => unfold fact; exact Nat.mul_pos (by omega) ih

private theorem fact_ge_one (n : Nat) : 1 ≤ fact n := fact_pos n

private theorem dvd_fact_of_pos_of_le (p n : Nat) (hp : 2 ≤ p) (hle : p ≤ n) : p ∣ fact n := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold fact
    if heq : p = n + 1 then
      rw [heq]; exact ⟨fact n, rfl⟩
    else
      have hle' : p ≤ n := by omega
      have ⟨k, hk⟩ := ih hle'
      exact ⟨(n + 1) * k, by rw [hk]; rw [Nat.mul_comm (n+1) (p * k), Nat.mul_assoc, Nat.mul_comm k (n+1)]⟩

/-- There is no largest prime (Euclid's infinity of primes). -/
-- ENGLISH: For any number, there exists a prime bigger than it. Primes are infinite.
theorem exists_prime_gt (n : Nat) : ∃ p, IsPrime p ∧ p > n := by
  --PROOF_START[exists_prime_gt]
  -- Consider fact n + 1
  have hge : 2 ≤ fact n + 1 := by have := fact_pos n; omega
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_dvd (fact n + 1) hge
  -- Show p > n by contradiction: if p ≤ n then p | fact n and p | (fact n + 1), so p | 1
  have hpgt : p > n := by
    if hle : p ≤ n then
      have hp2 := hp.1
      have hpfact : p ∣ fact n := dvd_fact_of_pos_of_le p n hp2 hle
      -- p | (fact n + 1) and p | fact n implies p | 1
      -- If p | a and p | b then p | (a - b) for Nat when b ≤ a
      have hpdvd1 : p ∣ 1 := by
        obtain ⟨a, ha⟩ := hpdvd
        obtain ⟨b, hb⟩ := hpfact
        -- fact n = p * b, fact n + 1 = p * a
        -- So p * a = p * b + 1, meaning p * (a - b) = 1
        -- We need: a = b + something where p * something = 1
        -- Actually: a ≥ b + 1 would give p * a ≥ p * (b+1) = p*b + p ≥ p*b + 2
        -- But p * a = p * b + 1, so a = b or a = b + ...
        -- With p ≥ 2: if a ≥ b+1 then p*a ≥ p*b + p ≥ p*b + 2 > p*b + 1 = p*a, contradiction
        -- If a ≤ b then p*a ≤ p*b < p*b + 1 = p*a, contradiction
        -- So actually this is directly contradictory!
        exfalso
        have : p * a = p * b + 1 := by omega
        have hab : a ≥ b + 1 ∨ a ≤ b := by omega
        cases hab with
        | inl h =>
          have hpa : p * a ≥ p * (b + 1) := Nat.mul_le_mul_left p h
          have hpb1 : p * (b + 1) = p * b + p := Nat.mul_succ p b
          omega
        | inr h =>
          have : p * a ≤ p * b := Nat.mul_le_mul_left p h
          omega
      have h5 : p ≤ 1 := Nat.le_of_dvd (by omega) hpdvd1
      omega
    else
      omega
  exact ⟨p, hp, hpgt⟩
  --PROOF_END[exists_prime_gt]

-- ============================================================
-- PRIME POWER PROPERTIES
-- ============================================================

/-- A prime squared is not prime. -/
-- ENGLISH: The square of a prime is composite (not prime).
theorem sq_not_prime (p : Nat) (hp : IsPrime p) : ¬IsPrime (p * p) := by
  --PROOF_START[sq_not_prime]
  intro hpp
  cases hpp.2 p ⟨p, rfl⟩ with
  | inl h => have := hp.1; omega
  | inr h =>
    -- p * p = p with p ≥ 2 is impossible
    have hp2 := hp.1
    have : p ≥ 1 := by omega
    have : p * p ≥ p * 2 := Nat.mul_le_mul_left p hp2
    omega
  --PROOF_END[sq_not_prime]

/-- If p is prime and p divides p^k for k ≥ 1, that's trivially true. -/
-- ENGLISH: A prime always divides its own powers.
theorem prime_dvd_pow_self (p k : Nat) (hp : IsPrime p) (hk : 1 ≤ k) : p ∣ p ^ k := by
  --PROOF_START[prime_dvd_pow_self]
  cases k with
  | zero => omega
  | succ n => exact ⟨p ^ n, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  --PROOF_END[prime_dvd_pow_self]

/-- If p is prime and p divides a^n, then p divides a. -/
-- ENGLISH: If a prime divides a perfect power, it must divide the base.
theorem prime_dvd_of_dvd_pow (p a n : Nat) (hp : IsPrime p) (hn : 1 ≤ n) (h : p ∣ a ^ n) : p ∣ a := by
  --PROOF_START[prime_dvd_of_dvd_pow]
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [Nat.pow_succ] at h
    cases prime_dvd_mul p (a ^ n) a hp h with
    | inl hpow =>
      cases n with
      | zero => simp [Nat.pow_zero] at hpow; obtain ⟨k, hk⟩ := hpow; have := hp.1; omega
      | succ m => exact ih (by omega) hpow
    | inr ha => exact ha
  --PROOF_END[prime_dvd_of_dvd_pow]

-- ============================================================
-- PRIMALITY TESTING BOUND
-- ============================================================

/-- To check if n is prime, you only need to check divisors up to √n. -/
-- ENGLISH: If n has no divisors between 2 and √n, it's prime. This is why trial division works.
theorem prime_of_no_small_factors (n : Nat) (hn : 2 ≤ n)
    (h : ∀ d, 2 ≤ d → d * d ≤ n → ¬(d ∣ n)) : IsPrime n := by
  --PROOF_START[prime_of_no_small_factors]
  constructor
  · exact hn
  · intro d hdvd
    -- d | n, need to show d = 1 ∨ d = n
    have hd_pos : 0 < d := by
      cases d with
      | zero => obtain ⟨k, hk⟩ := hdvd; omega
      | succ d => omega
    have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    if hd1 : d = 1 then left; exact hd1
    else if hdn : d = n then right; exact hdn
    else
      exfalso
      have hd_ge2 : 2 ≤ d := by omega
      have ⟨e, he⟩ := hdvd  -- n = d * e
      have he' : d * e = n := by omega
      have hdvd' : d ∣ n := ⟨e, he⟩
      have he_ge2 : 2 ≤ e := by
        cases e with
        | zero => omega
        | succ e => cases e with
          | zero => omega  -- e=1 means d=n
          | succ e => omega
      if hdd : d * d ≤ n then
        exact h d hd_ge2 hdd hdvd'
      else
        -- d * d > n, need e * e ≤ n
        have hee : e * e ≤ n := by
          -- d * d > n = d * e, so d > e
          have hde : e ≤ d := by
            if hed : d < e then
              have := Nat.mul_le_mul_right d (Nat.le_of_lt hed)
              -- d * d < e * d but we need d * e form
              have : d * d ≤ d * e := by
                rw [Nat.mul_comm d e]; exact Nat.mul_le_mul_right d (Nat.le_of_lt hed)
              omega
            else omega
          -- e * e ≤ e * d ≤ d * e = n
          calc e * e ≤ e * d := Nat.mul_le_mul_left e hde
            _ = d * e := Nat.mul_comm e d
            _ = n := he'
        have he_dvd : e ∣ n := ⟨d, by rw [← he']; rw [Nat.mul_comm]⟩
        exact h e he_ge2 hee he_dvd
  --PROOF_END[prime_of_no_small_factors]

/-- 5 is prime (via the small factors test). -/
-- ENGLISH: 5 is a prime number because no number from 2 to √5 divides it.
theorem five_is_prime : IsPrime 5 := by
  --PROOF_START[five_is_prime]
  constructor; · omega
  intro d hd; have := Nat.le_of_dvd (by omega) hd; obtain ⟨k, hk⟩ := hd
  cases d with | zero => omega | succ n =>
  cases n with | zero => left; rfl | succ m =>
  cases m with | zero => exfalso; omega | succ l =>
  cases l with | zero => exfalso; omega | succ j =>
  cases j with | zero => right; omega | succ i => omega
  --PROOF_END[five_is_prime]

end ProofFarm.Primes
