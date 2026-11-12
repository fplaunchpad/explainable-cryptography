import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

/-!
# Perfect (adversarial) indistinguishability

A formalization of Definition 2.6 from Katz and Lindell,
*Introduction to Modern Cryptography*.
-/

namespace ExplainableCrypto.KatzLindell

/-- A private-key encryption scheme with message space `M`, key space `K`,
and ciphertext space `C`. Key generation and encryption are randomized
(they return distributions); decryption is deterministic. -/
structure EncScheme (M K C : Type) where
  keygen : PMF K
  encrypt : K → M → PMF C
  decrypt : K → C → M

/-- An adversary against the `PrivKeav` experiment. Definition 2.6 notes we
may assume WLOG that `A` is deterministic and stateless: its first move is
a fixed pair of messages `(m₀, m₁)` chosen with no input at all, and its
second move is a function from the challenge ciphertext to a guessed bit. -/
structure Adversary (M C : Type) where
  choose : M × M
  guess : C → Bool

variable {M K C : Type}

/-- The adversarial indistinguishability experiment `PrivKeav_{A,S}`,
as a distribution over its {0,1}-valued outcome. (Named `S` for "scheme"
since `Π` is reserved by Lean for dependent function types.) -/
noncomputable def PrivKeav (S : EncScheme M K C) (A : Adversary M C) : PMF Bool := do
  let k ← S.keygen
  let b ← PMF.uniformOfFintype Bool
  let c ← S.encrypt k (if b then A.choose.2 else A.choose.1)
  pure (A.guess c == b)

/-- **Definition 2.6.** `S` is perfectly indistinguishable if every
adversary succeeds (guesses `b` correctly) with probability exactly `1/2`. -/
def PerfectlyIndistinguishable (S : EncScheme M K C) : Prop :=
  ∀ A : Adversary M C, PrivKeav S A true = (1 / 2 : ENNReal)

end ExplainableCrypto.KatzLindell
