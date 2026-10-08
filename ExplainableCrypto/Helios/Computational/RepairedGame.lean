import ExplainableCrypto.Helios.Computational.RepairedSampling
import ExplainableCrypto.Helios.Computational.BallotSecrecyGame

/-! Repaired execution in the same public stateful-adversary game interface.
The checked theorem is probability-one rejection of the known copying submission.
No statement here asserts privacy against arbitrary adversaries. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F G State : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

noncomputable def repairedBallotWorld (hashes : StrongCryptoHashes F G) (g : G)
    (adversary : BallotAdversary F G State) (vote : Bool) : ProbComp Bool := do
  let secret ← sampleNonzero F
  let keyNonce ← sampleNonzero F
  let decryptionNonces ← drawNoncePair F
  let pair ← drawHonestPair F
  let beforeTally := makeRepairedPrefix hashes g secret keyNonce vote pair.1 pair.2
  let (submission, savedState) ← adversary.castBallot beforeTally
  let view := finishRepairedElection hashes secret ![decryptionNonces.1, decryptionNonces.2]
    beforeTally submission
  adversary.guessVote savedState view

noncomputable def repairedBallotSecrecyGame (hashes : StrongCryptoHashes F G) (g : G)
    (adversary : BallotAdversary F G State) : ProbComp Bool := do
  let vote ← uniformSample Bool
  let guess ← repairedBallotWorld hashes g adversary vote
  pure (decide (guess = vote))

noncomputable def repairedAttackWorld (hashes : StrongCryptoHashes F G) (g : G)
    (vote : Bool) : ProbComp (PublicResult F G) := do
  let secret ← sampleNonzero F
  let keyNonce ← sampleNonzero F
  let decryptionNonces ← drawNoncePair F
  let pair ← drawHonestPair F
  pure (executeRepairedAttack hashes g secret keyNonce ![decryptionNonces.1, decryptionNonces.2]
    vote pair.1 pair.2)

theorem repairedAttackWorld_rejection_probability (hashes : StrongCryptoHashes F G) (g : G)
    (vote : Bool) : Pr[fun view => view.decision = .reusedCiphertext | repairedAttackWorld hashes g vote] = 1 := by
  apply probEvent_eq_one_iff.mpr
  constructor
  · simp [repairedAttackWorld, drawHonestPair, drawHonestCoins, drawTriple, drawNoncePair, sampleNonzero]
  · intro view hv
    simp only [repairedAttackWorld, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hv
    obtain ⟨secret, _, keyNonce, _, decryptionNonces, _, pair, _, rfl⟩ := hv
    exact executeRepairedAttack_rejected hashes g secret keyNonce _ vote pair.1 pair.2

#print axioms repairedAttackWorld_rejection_probability

end ExplainableCrypto.Helios.Computational
