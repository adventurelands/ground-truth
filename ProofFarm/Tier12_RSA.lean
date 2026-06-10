/-
  ProofFarm.Tier12_RSA
  RSA encryption correctness: the capstone.
  From 2+2=4 to proving RSA works, in pure Lean 4, no Mathlib.
-/
import ProofFarm.Tier11_RSABridge

namespace ProofFarm.RSA

-- ============================================================
-- RSA DEFINITIONS
-- ============================================================

/-- RSA public key: modulus n = p*q and encryption exponent e. -/
structure RSAPublicKey where
  p : Nat
  q : Nat
  e : Nat
  hp : Primes.IsPrime p
  hq : Primes.IsPrime q
  hne : p ≠ q

/-- RSA encryption: c = m^e mod n. -/
def encrypt (key : RSAPublicKey) (m : Nat) : Nat :=
  m ^ key.e % (key.p * key.q)

/-- RSA decryption: m = c^d mod n. -/
def decrypt (p q d : Nat) (c : Nat) : Nat :=
  c ^ d % (p * q)

-- ============================================================
-- RSA CORRECTNESS: THE CAPSTONE
-- ============================================================

/-- RSA correctness: for distinct primes p, q, if d*e ≡ 1 mod (p-1)(q-1),
    then m^(d*e) ≡ m mod p*q.
    This is THE theorem. Everything from Tier 1 through Tier 11 builds to this. -/
-- ENGLISH: RSA encryption followed by decryption recovers the original message. This proves that the most widely used public-key cryptosystem in the world is mathematically correct.
theorem rsa_correctness (m d e p q : Nat)
    (hp : Primes.IsPrime p) (hq : Primes.IsPrime q) (hne : p ≠ q)
    (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1))) :
    m ^ (d * e) % (p * q) = m % (p * q) := by
  --PROOF_START[rsa_correctness]
  have hmodp : m ^ (d * e) % p = m % p := RSABridge.rsa_mod_p m d e p q hp hde
  have hmodq : m ^ (d * e) % q = m % q := RSABridge.rsa_mod_q m d e p q hq hde
  have hcop : GCD.Coprime p q := CRT.primes_coprime p q hp hq hne
  exact CRT.crt_combine (m ^ (d * e)) m p q hcop hmodp hmodq
  --PROOF_END[rsa_correctness]

/-- RSA encrypt-then-decrypt recovers the message (for m < n). -/
-- ENGLISH: If your message is smaller than n = p*q, encrypting then decrypting gives you back exactly your message. This is what every RSA implementation relies on.
theorem rsa_encrypt_decrypt (m d e p q : Nat)
    (hp : Primes.IsPrime p) (hq : Primes.IsPrime q) (hne : p ≠ q)
    (hm : m < p * q)
    (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1))) :
    decrypt p q d (encrypt ⟨p, q, e, hp, hq, hne⟩ m) = m := by
  --PROOF_START[rsa_encrypt_decrypt]
  simp only [encrypt, decrypt]
  -- Goal: (m ^ e % (p * q)) ^ d % (p * q) = m
  rw [← Nat.pow_mod (m ^ e) d (p * q)]
  -- Now: (m ^ e) ^ d % (p * q) = m
  rw [← Nat.pow_mul]
  -- Now: m ^ (e * d) % (p * q) = m
  have hed : ∃ k, e * d = 1 + k * ((p - 1) * (q - 1)) := by
    obtain ⟨k, hk⟩ := hde
    exact ⟨k, by rw [Nat.mul_comm e d]; exact hk⟩
  rw [rsa_correctness m e d p q hp hq hne hed]
  exact Nat.mod_eq_of_lt hm
  --PROOF_END[rsa_encrypt_decrypt]

/-- RSA decrypt-then-encrypt also works (commutativity of RSA). -/
-- ENGLISH: You can also decrypt first and encrypt second; the math works both ways. This property is used in RSA signatures.
theorem rsa_decrypt_encrypt (m d e p q : Nat)
    (hp : Primes.IsPrime p) (hq : Primes.IsPrime q) (hne : p ≠ q)
    (hm : m < p * q)
    (hde : ∃ k, d * e = 1 + k * ((p - 1) * (q - 1)))
    (hed : ∃ k, e * d = 1 + k * ((p - 1) * (q - 1))) :
    encrypt ⟨p, q, e, hp, hq, hne⟩ (decrypt p q d m) = m := by
  --PROOF_START[rsa_decrypt_encrypt]
  simp only [encrypt, decrypt]
  -- Goal: (m ^ d % (p * q)) ^ e % (p * q) = m
  rw [← Nat.pow_mod (m ^ d) e (p * q)]
  rw [← Nat.pow_mul]
  -- Now: m ^ (d * e) % (p * q) = m
  rw [rsa_correctness m d e p q hp hq hne hde]
  exact Nat.mod_eq_of_lt hm
  --PROOF_END[rsa_decrypt_encrypt]

/-- The exponent condition is satisfiable: given coprime e and phi(n), d exists. -/
-- ENGLISH: You can always find a decryption key d for any valid encryption key e. This is why RSA key generation works.
theorem rsa_key_exists (e p q : Nat)
    (hp : Primes.IsPrime p) (hq : Primes.IsPrime q) (hne : p ≠ q)
    (he : 1 < e) (hephi : GCD.Coprime e ((p - 1) * (q - 1)))
    (hphi : 1 < (p - 1) * (q - 1)) :
    ∃ d : Nat, ∃ k : Nat, d * e = 1 + k * ((p - 1) * (q - 1)) := by
  --PROOF_START[rsa_key_exists]
  -- From mod_inverse_exists: there exists d with e * d % phi = 1
  -- i.e. e * d = 1 + k * phi for some k
  have hinv := Bezout.mod_inverse_exists e ((p - 1) * (q - 1)) hphi hephi
  obtain ⟨d, _, hd⟩ := hinv
  -- hd : (e * d) % ((p-1)*(q-1)) = 1
  have hdiv := Nat.div_add_mod (e * d) ((p - 1) * (q - 1))
  rw [hd] at hdiv
  -- hdiv : ((p-1)*(q-1)) * (e*d / ((p-1)*(q-1))) + 1 = e * d
  let k := e * d / ((p - 1) * (q - 1))
  have hk : (p - 1) * (q - 1) * k + 1 = e * d := hdiv
  have goal : d * e = 1 + k * ((p - 1) * (q - 1)) := by
    rw [Nat.mul_comm d e, Nat.mul_comm k]
    omega
  exact ⟨d, k, goal⟩
  --PROOF_END[rsa_key_exists]

/-- RSA concrete test: 2^3 mod 33 = 8, then 8^7 mod 33 = 2. -/
-- ENGLISH: A concrete numerical check: encrypting 2 with key (e=3, n=33) gives 8, and decrypting 8 with key (d=7, n=33) gives back 2.
theorem rsa_example_encrypt_2 : (2 ^ 3) % 33 = 8 := by
  --PROOF_START[rsa_example_encrypt_2]
  native_decide
  --PROOF_END[rsa_example_encrypt_2]

/-- RSA concrete test: decryption recovers the message. -/
-- ENGLISH: Decrypting the ciphertext 8 with d=7, n=33 gives back the original message 2.
theorem rsa_example_decrypt_8 : (8 ^ 7) % 33 = 2 := by
  --PROOF_START[rsa_example_decrypt_8]
  native_decide
  --PROOF_END[rsa_example_decrypt_8]

end ProofFarm.RSA
