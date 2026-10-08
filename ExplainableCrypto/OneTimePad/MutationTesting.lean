import Mathlib.Probability.Distributions.Uniform

/-!
# Mutation testing a one-time pad

This file takes the mutation-testing pattern from `ExplainableCrypto/MutationTesting.lean` into a
real cryptographic example. It develops just enough probability to say what
perfect secrecy means, proves the one-time pad secure, and then gives checked
witnesses for plausible mistakes in both the definition and the construction.

The example deliberately keeps the cryptographic interface small. Mathlib
supplies finite probability mass functions; everything specific to encryption,
security, mutation, and attacks remains visible here.
-/

open scoped ENNReal
open PMF

namespace ExplainableCrypto.OneTimePad

/-! ## Ciphers and their intended specification -/

abbrev Block (n : Nat) := BitVec n

/-- `BitVec n` is finite: its values are exactly the natural numbers below
`2^n`. Lean's core library supplies the equivalence; this instance exposes it
to Mathlib's finite uniform distribution. -/
def blockEquivFin (n : Nat) : Block n ≃ Fin (2 ^ n) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv := BitVec.ofFin_toFin
  right_inv := BitVec.toFin_ofFin

instance (n : Nat) : Fintype (Block n) :=
  Fintype.ofEquiv (Fin (2 ^ n)) (blockEquivFin n).symm

@[simp] theorem card_block (n : Nat) : Fintype.card (Block n) = 2 ^ n :=
  by simpa using Fintype.card_congr (blockEquivFin n)

/-- A finite cipher with a key generator. Keeping correctness out of the
structure is intentional: correctness is one part of the specification and can
therefore itself be accidentally omitted. -/
structure Cipher (n : Nat) where
  keygen : PMF (Block n)
  encrypt : Block n → Block n → Block n
  decrypt : Block n → Block n → Block n

/-- Encryption followed by decryption returns the original message. -/
def Correct {n : Nat} (S : Cipher n) : Prop :=
  ∀ k m, S.decrypt k (S.encrypt k m) = m

/-- The ciphertext distribution for a fixed message. -/
noncomputable def ciphertextDist {n : Nat} (S : Cipher n) (m : Block n) :
    PMF (Block n) :=
  PMF.map (fun k => S.encrypt k m) S.keygen

/-- The row-equality form of perfect secrecy: every two messages induce the
same probability for every ciphertext. -/
def PerfectlySecret {n : Nat} (S : Cipher n) : Prop :=
  ∀ m₀ m₁ c, ciphertextDist S m₀ c = ciphertextDist S m₁ c

/-- The intended definition asks for both functional correctness and secrecy. -/
def Intended {n : Nat} (S : Cipher n) : Prop :=
  Correct S ∧ PerfectlySecret S

/-! ## The one-time pad -/

/-- A uniformly sampled `n`-bit key. -/
noncomputable def uniformKey (n : Nat) : PMF (Block n) :=
  PMF.uniformOfFintype (Block n)

/-- A computable count of the keys that map `m` to `c`. Visualizations use
this finite table instead of attempting to execute Mathlib's noncomputable
real-number representation of probabilities. -/
def matchingKeyCount {n : Nat}
    (encrypt : Block n → Block n → Block n) (m c : Block n) : Nat :=
  (Finset.univ.filter fun k => encrypt k m = c).card

/-- Under a uniform key, the probability of a ciphertext is its matching-key
count divided by the number of keys. This is the checked bridge from the
computable tables used by the widget to the PMF specification above. -/
theorem uniform_probability_eq_count {n : Nat}
    (encrypt : Block n → Block n → Block n) (m c : Block n) :
    PMF.map (fun k => encrypt k m) (uniformKey n) c =
      matchingKeyCount encrypt m c / Fintype.card (Block n) := by
  simp [matchingKeyCount, uniformKey, PMF.map_apply, div_eq_mul_inv]
  rw [Finset.sum_ite]
  simp [eq_comm, Finset.sum_const, nsmul_eq_mul]

/-- The one-time pad: encryption and decryption are both XOR. -/
noncomputable def oneTimePad (n : Nat) : Cipher n where
  keygen := uniformKey n
  encrypt k m := k ^^^ m
  decrypt k c := k ^^^ c

theorem oneTimePad_correct (n : Nat) : Correct (oneTimePad n) := by
  intro k m
  change k ^^^ (k ^^^ m) = m
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Solving `c = k ⊕ m` for the unique key gives `k = c ⊕ m`. -/
lemma xor_equation {n : Nat} (k m c : Block n) :
    c = k ^^^ m ↔ k = c ^^^ m := by
  constructor <;> intro h
  · rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem oneTimePad_perfectlySecret (n : Nat) :
    PerfectlySecret (oneTimePad n) := by
  intro m₀ m₁ c
  simp [ciphertextDist, oneTimePad, uniformKey, PMF.map_apply, xor_equation]

theorem oneTimePad_meets_intended (n : Nat) : Intended (oneTimePad n) :=
  ⟨oneTimePad_correct n, oneTimePad_perfectlySecret n⟩

/-! ## Checked attacks

For this definition, an attack is especially concrete: two messages and one
ciphertext whose probabilities differ. The record stores the witness and the
checked inequality, so merely failing to find an attack proves nothing.
-/

structure SecrecyAttack {n : Nat} (S : Cipher n) where
  leftMessage : Block n
  rightMessage : Block n
  observedCiphertext : Block n
  distinguishes :
    ciphertextDist S leftMessage observedCiphertext ≠
      ciphertextDist S rightMessage observedCiphertext

theorem attack_refutes_secrecy {n : Nat} {S : Cipher n}
    (attack : SecrecyAttack S) : ¬ PerfectlySecret S := by
  intro h
  exact attack.distinguishes
    (h attack.leftMessage attack.rightMessage attack.observedCiphertext)

/-! ## Definition mutants

The first two mutants each drop half of the intended definition. Both are
strictly weaker: every intended cipher satisfies them, but a small construction
separates each mutant from `Intended`.
-/

def CorrectnessOnly {n : Nat} (S : Cipher n) : Prop := Correct S
def SecrecyOnly {n : Nat} (S : Cipher n) : Prop := PerfectlySecret S

theorem intended_implies_correctnessOnly {n : Nat} (S : Cipher n) :
    Intended S → CorrectnessOnly S := And.left

theorem intended_implies_secrecyOnly {n : Nat} (S : Cipher n) :
    Intended S → SecrecyOnly S := And.right

/-- A plausible but disastrous construction: transmit the message unchanged.
It decrypts correctly, but the ciphertext reveals the message. -/
noncomputable def cleartextCipher (n : Nat) : Cipher n where
  keygen := uniformKey n
  encrypt _ m := m
  decrypt _ c := c

theorem cleartext_correct (n : Nat) : CorrectnessOnly (cleartextCipher n) := by
  intro k m
  rfl

/-- For one-bit messages, observing `0` distinguishes plaintext `0` from `1`. -/
def cleartext_attack : SecrecyAttack (cleartextCipher 1) where
  leftMessage := 0
  rightMessage := 1
  observedCiphertext := 0
  distinguishes := by
    simp [ciphertextDist, cleartextCipher, uniformKey, PMF.map_apply]

theorem cleartext_fails_intended : ¬ Intended (cleartextCipher 1) := by
  intro h
  exact attack_refutes_secrecy cleartext_attack h.right

/-- Another plausible mistake: always emit zero. Its output is independent of
the message, but it cannot correctly decrypt nonzero messages. -/
noncomputable def constantCipher (n : Nat) : Cipher n where
  keygen := uniformKey n
  encrypt _ _ := 0
  decrypt _ _ := 0

theorem constant_is_secret (n : Nat) : SecrecyOnly (constantCipher n) := by
  intro m₀ m₁ c
  rfl

theorem constant_not_correct : ¬ Correct (constantCipher 1) := by
  intro h
  have := h 0 1
  exact (by decide : (0 : Block 1) ≠ 1) this

theorem constant_fails_intended : ¬ Intended (constantCipher 1) := by
  intro h
  exact constant_not_correct h.left

/-! ## Construction mutant: reusing the pad

The one-time pad is secure only when a fresh key is used once. If the same key
encrypts two messages, XORing the two ciphertexts cancels the key and reveals
the XOR of the messages. We express this as a distribution over ciphertext
pairs and give a checked two-bit witness.
-/

noncomputable def reusedKeyDist {n : Nat} (m₀ m₁ : Block n) :
    PMF (Block n × Block n) :=
  PMF.map (fun k => (k ^^^ m₀, k ^^^ m₁)) (uniformKey n)

structure ReuseAttack (n : Nat) where
  leftMessages : Block n × Block n
  rightMessages : Block n × Block n
  observedCiphertexts : Block n × Block n
  distinguishes :
    reusedKeyDist leftMessages.1 leftMessages.2 observedCiphertexts ≠
      reusedKeyDist rightMessages.1 rightMessages.2 observedCiphertexts

/-- Reusing a two-bit key distinguishes `(00, 00)` from `(00, 11)` by
observing `(00, 00)`: the former occurs with probability `1/4`, the latter
cannot occur. -/
def reuse_attack : ReuseAttack 2 where
  leftMessages := (0, 0)
  rightMessages := (0, 3)
  observedCiphertexts := (0, 0)
  distinguishes := by
    have eq_swap (a b : Block 2) : a = b ↔ b = a := eq_comm
    simp [reusedKeyDist, uniformKey, PMF.map_apply, eq_swap]
    have impossible (a : Block 2) : ¬(a = 0 ∧ 0 = a ^^^ 3) := by
      rintro ⟨rfl, h⟩
      exact (by decide : (0 : Block 2) ≠ 0 ^^^ 3) h
    intro hEq
    have hzero :
        (∑ a : Block 2, if a = 0 ∧ 0 = a ^^^ 3
          then (4 : ENNReal)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg (impossible a)]
    have : (4 : ENNReal)⁻¹ = 0 := hEq.trans hzero
    norm_num at this

/-! ## Coverage report

This remains an explicit catalogue. Each entry is justified above, but the
list itself is not yet proof-carrying or generated automatically.
-/

inductive Status where
  | separated
  | killed
  | secure
  deriving Repr

def definitionResults : List (String × Status) :=
  [("correctness only", .separated),
   ("secrecy only", .separated)]

def constructionResults : List (String × Status) :=
  [("cleartext encryption", .killed),
   ("constant ciphertext", .killed),
   ("reused pad", .killed),
   ("one-time pad", .secure)]

#eval definitionResults
#eval constructionResults

end ExplainableCrypto.OneTimePad
