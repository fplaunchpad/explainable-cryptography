import ExplainableCrypto.Helios.Computational.AttackGame
import ExplainableCrypto.Helios.Computational.Controls

/-! Independent p=23, q=11, g=2, h=8 execution fixtures. Hash challenges are
fixed at 5; these are arithmetic/transcript controls, not hardness or SHA tests. -/

namespace ExplainableCrypto.Helios.Computational.ExecutionControls

abbrev Scalar := ZMod 11

def hashes : CryptoHashes Scalar Scalar :=
  ⟨fun _ => 5, fun _ => 5, fun _ => 5, fun _ => 37⟩

def aliceCoins : HonestCoins Scalar := ⟨![1, 2], fun _ => 4, fun _ => 2, fun _ => 3⟩
def bobCoins : HonestCoins Scalar := ⟨![4, 5], fun _ => 4, fun _ => 2, fun _ => 3⟩

def fixture (vote : Bool) : PublicResult Scalar Scalar :=
  executeAttack hashes 1 3 4 ![4, 4] vote aliceCoins bobCoins

def encode (value : Scalar) : Nat := 2 ^ value.val % 23

theorem key_proof_matches_literal_transcript :
    (encode (schnorrProof hashes.key 1 (3 : Scalar) 4).commitment,
      (schnorrProof hashes.key 1 (3 : Scalar) 4).response.val) = (16, 8) := by decide

theorem literal_key_proof_valid : 2 ^ 8 % 23 = 16 * 8 ^ 5 % 23 := by decide
theorem changed_key_response_rejected : 2 ^ 9 % 23 ≠ 16 * 8 ^ 5 % 23 := by decide

/-- Nonces 1,2 and 4,5 give tally randomness 8. With secret 3, its share is
3^3 = 4 modulo 23; proof nonce 4 yields commitments 16 and 12, response 8. -/
theorem decryption_proof_matches_literal_transcript :
    (encode ((fixture false).decryptionProofs 0).commitment.1,
      encode ((fixture false).decryptionProofs 0).commitment.2,
      ((fixture false).decryptionProofs 0).response.val) = (16, 12, 8) := by decide

theorem literal_decryption_proof_valid :
    2 ^ 8 % 23 = 16 * 8 ^ 5 % 23 ∧ 3 ^ 8 % 23 = 12 * 4 ^ 5 % 23 := by decide

theorem changed_decryption_commitment_rejected :
    3 ^ 8 % 23 ≠ 13 * 4 ^ 5 % 23 := by decide

theorem concrete_worlds_publish_distinct_tallies :
    (fixture false).decodedTally 0 = some 1 ∧ (fixture true).decodedTally 0 = some 2 ∧
      encode ((fixture false).encryptedTally 0).1 = 3 ∧
      encode ((fixture false).decryptionShares 0) = 4 := by decide

theorem honest_ballots_and_attack_are_accepted :
    (fixture false).beforeTally.honestDecisions = (.accepted, .accepted) ∧
      (fixture false).decision = .accepted ∧ (fixture false).board.length = 3 := by decide

def coincidentCoins : HonestCoins Scalar :=
  ⟨fun _ => 1, fun _ => 4, fun _ => 2, fun _ => 3⟩

def rejectedHonestRun : PublicResult Scalar Scalar :=
  executeAttack hashes 1 3 4 ![4, 4] false coincidentCoins coincidentCoins

theorem rejection_retains_board_and_tally_continues :
    rejectedHonestRun.beforeTally.honestDecisions = (.accepted, .reusedCiphertext) ∧
      rejectedHonestRun.decision = .accepted ∧ rejectedHonestRun.board.length = 2 ∧
      rejectedHonestRun.decodedTally 0 = some 0 := by decide

def corruptedBallot : Ballot Scalar Scalar 2 :=
  let b := honestBallot hashes.ballot 1 3 false aliceCoins
  { b with overall := { b.overall with zero :=
    { b.overall.zero with response := b.overall.zero.response + 1 } } }

theorem invalid_proof_is_rejected :
    submit hashes.ballot (1 : Scalar) 3 0 [] corruptedBallot = (.invalidProof, []) := by
  have h : ¬ corruptedBallot.Valid hashes.ballot 1 3 := by decide
  simp [submit, h]

def freshAbstentionRun (vote : Bool) : PublicResult Scalar Scalar :=
  let beforeTally := makePrefix hashes 1 3 4 vote aliceCoins bobCoins
  let coins : HonestCoins Scalar := ⟨![9, 10], fun _ => 4, fun _ => 2, fun _ => 3⟩
  finishElection hashes 3 ![4, 4] beforeTally (honestBallot hashes.ballot 1 3 false coins)

/-- Independent arithmetic: v + (1-v) + 0 = 1 in both worlds. An additional
fresh abstention does not have the copying effect of the malicious ballot. -/
theorem fresh_abstention_has_no_copying_effect :
    (freshAbstentionRun false).decodedTally 0 = some 1 ∧
      (freshAbstentionRun true).decodedTally 0 = some 1 ∧
      (freshAbstentionRun false).decision = .accepted ∧
      (freshAbstentionRun true).decision = .accepted := by decide

#print axioms fresh_abstention_has_no_copying_effect
#print axioms key_proof_matches_literal_transcript
#print axioms literal_key_proof_valid
#print axioms changed_key_response_rejected
#print axioms decryption_proof_matches_literal_transcript
#print axioms literal_decryption_proof_valid
#print axioms changed_decryption_commitment_rejected
#print axioms concrete_worlds_publish_distinct_tallies
#print axioms honest_ballots_and_attack_are_accepted
#print axioms rejection_retains_board_and_tally_continues
#print axioms invalid_proof_is_rejected

end ExplainableCrypto.Helios.Computational.ExecutionControls
