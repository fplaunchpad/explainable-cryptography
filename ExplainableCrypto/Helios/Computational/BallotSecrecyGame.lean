import ExplainableCrypto.Helios.Computational.AttackProbability

/-! A stateful adversary interface for the concrete three-voter game. The
adversary receives public messages at both interaction points and keeps its own
state; the sampled key, challenge bit and honest coins remain challenger-local.
The theorem instantiates a successful attack, not security for this interface. -/

namespace ExplainableCrypto.Helios.Computational

structure BallotAdversary (F G State : Type) where
  castBallot : PublicPrefix F G → ProbComp (Ballot F G 2 × State)
  guessVote : State → PublicResult F G → ProbComp Bool

variable {F G State : Type} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

noncomputable def ballotWorld (hashes : CryptoHashes F G) (g : G)
    (adversary : BallotAdversary F G State) (vote : Bool) : ProbComp Bool := do
  let secret ← sampleNonzero F
  let keyNonce ← sampleNonzero F
  let decryptionNonces ← drawNoncePair F
  let pair ← drawHonestPair F
  let beforeTally := makePrefix hashes g secret keyNonce vote pair.1 pair.2
  let (submission, savedState) ← adversary.castBallot beforeTally
  let view := finishElection hashes secret ![decryptionNonces.1, decryptionNonces.2]
    beforeTally submission
  adversary.guessVote savedState view

noncomputable def ballotSecrecyGame (hashes : CryptoHashes F G) (g : G)
    (adversary : BallotAdversary F G State) : ProbComp Bool := do
  let vote ← uniformSample Bool
  let guess ← ballotWorld hashes g adversary vote
  pure (decide (guess = vote))

def proofReuseAdversary (hashes : CryptoHashes F G) : BallotAdversary F G Unit where
  castBallot beforeTally := pure (proofReuseSubmission hashes beforeTally, ())
  guessVote _ view := pure (attackDistinguisher view)

theorem instantiated_attack_game (hashes : CryptoHashes F G) (g : G) :
    ballotSecrecyGame hashes g (proofReuseAdversary hashes) = attackGuessingGame hashes g := by
  simp only [ballotSecrecyGame, ballotWorld, proofReuseAdversary, attackGuessingGame,
    attackWorld, executeAttack, bind_assoc, pure_bind]

open OracleComp

theorem ballotSecrecyGame_proofReuse_success (hashes : CryptoHashes F G) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) :
    1 - 6 * noncePointBound F ≤
      Pr[= true | ballotSecrecyGame hashes g (proofReuseAdversary hashes)] := by
  rw [instantiated_attack_game]
  exact proofReuse_attack_success hashes g hg

#print axioms instantiated_attack_game
#print axioms ballotSecrecyGame_proofReuse_success

end ExplainableCrypto.Helios.Computational
