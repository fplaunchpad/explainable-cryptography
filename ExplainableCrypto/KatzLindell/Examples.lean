import ExplainableCrypto.KatzLindell.Basic

/-!
# Sanity checks for `PerfectlyIndistinguishable`

Two toy schemes on a single bit:
* `otpBit`, the 1-bit one-time pad, against which we check that one
  concrete adversary succeeds with probability exactly `1/2`;
* `leakyBit`, a scheme whose encryption ignores the key entirely, against
  which we exhibit an adversary that succeeds with probability `1`,
  showing `PerfectlyIndistinguishable` is a real (non-vacuous) constraint.
-/

namespace ExplainableCrypto.KatzLindell

/-- The one-time pad on a single bit: the key is a uniformly random bit,
and encryption XORs it with the message. -/
noncomputable def otpBit : EncScheme Bool Bool Bool where
  keygen := PMF.uniformOfFintype Bool
  encrypt k m := pure (Bool.xor k m)
  decrypt k c := Bool.xor k c

/-- Sanity check: decryption really does invert encryption (this is a claim
about the underlying bits, not about the `PMF` machinery, so `decide` can
just check all `2 × 2` cases). -/
example : ∀ k m, otpBit.decrypt k (Bool.xor k m) = m := by decide

/-- A concrete adversary: it commits to distinguishing `false` from `true`,
and guesses by reading the ciphertext bit directly. -/
def sampleAdv : Adversary Bool Bool where
  choose := (false, true)
  guess c := c

/-- Against `otpBit`, `sampleAdv` succeeds with probability exactly `1/2` —
the key's randomness masks the challenge bit completely. -/
example : PrivKeav otpBit sampleAdv true = (1 / 2 : ENNReal) := by
  simp [PrivKeav, sampleAdv, otpBit, Bind.bind, Pure.pure, PMF.bind_apply,
    PMF.pure_apply, tsum_fintype]
  rw [ENNReal.inv_two_add_inv_two, mul_one]

/-- A broken scheme: encryption ignores the key completely, so the
ciphertext just *is* the message. -/
noncomputable def leakyBit : EncScheme Bool Bool Bool where
  keygen := PMF.uniformOfFintype Bool
  encrypt _ m := pure m
  decrypt _ c := c

/-- An adversary that exploits the leak: it picks two distinct messages and
reads the ciphertext off as its guess directly. -/
def leakyAdv : Adversary Bool Bool where
  choose := (false, true)
  guess c := c

/-- Against `leakyBit`, `leakyAdv` succeeds with probability `1`, not `1/2` —
so `leakyBit` is **not** perfectly indistinguishable. This is the negative
sanity check: the definition actually rules something out. -/
theorem leakyBit_not_perfectlyIndistinguishable :
    ¬ PerfectlyIndistinguishable leakyBit := by
  intro h
  have := h leakyAdv
  simp [PrivKeav, leakyAdv, leakyBit, Bind.bind, Pure.pure, PMF.pure_apply] at this
  rw [eq_comm, ENNReal.inv_eq_one] at this
  norm_num at this

end ExplainableCrypto.KatzLindell
