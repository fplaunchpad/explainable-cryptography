import ExplainableCrypto.Helios.Computational.RepairedExecution
import ExplainableCrypto.Helios.Computational.WeakProofMalleability
import ExplainableCrypto.Helios.Computational.ExecutionControls

/-! Independently calculated modulo-23 repair controls. The nonconstant hash
below is a test function, not a cryptographic random oracle or SHA instance. -/

namespace ExplainableCrypto.Helios.Computational.RepairControls

abbrev Scalar := ZMod 11
open ExecutionControls (aliceCoins bobCoins encode)

local instance (hash : Hash Scalar Scalar) (g pk : Scalar) (ct : Ciphertext Scalar)
    (p : Proof01 Scalar Scalar) : Decidable (p.Valid hash g pk ct) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

local instance (hash : StatementHash Scalar Scalar) (g pk : Scalar) (ct : Ciphertext Scalar)
    (p : Proof01 Scalar Scalar) : Decidable (p.StrongValid hash g pk ct) := by
  unfold Proof01.StrongValid
  infer_instance

def hashes : StrongCryptoHashes Scalar Scalar where
  ballot g pk ct commitments := g + pk + ct.1 + ct.2 +
    commitments.1.1 + commitments.1.2 + commitments.2.1 + commitments.2.2
  key g pk commitment := g + pk + commitment
  decryption g pk ct share commitment := g + pk + ct.1 + ct.2 + share + commitment.1 + commitment.2
  fingerprint _ := 37

def fixture (vote : Bool) : PublicResult Scalar Scalar :=
  executeRepairedAttack hashes 1 3 4 ![4, 4] vote aliceCoins bobCoins

theorem honest_valid_attack_rejected_and_tally_preserved :
    (fixture false).beforeTally.honestDecisions = (.accepted, .accepted) ∧
    (fixture true).beforeTally.honestDecisions = (.accepted, .accepted) ∧
    (fixture false).decision = .reusedCiphertext ∧
    (fixture true).decision = .reusedCiphertext ∧
    (fixture false).board.length = 2 ∧ (fixture true).board.length = 2 ∧
    (fixture false).decodedTally 0 = some 1 ∧ (fixture true).decodedTally 0 = some 1 ∧
    (fixture false).decodedTally 1 = some 0 ∧ (fixture true).decodedTally 1 = some 0 := by decide

theorem literal_repaired_tally_and_share :
    (encode ((fixture false).encryptedTally 0).1,
      encode ((fixture false).encryptedTally 0).2,
      encode ((fixture false).decryptionShares 0)) = (9, 9, 16) := by decide

theorem literal_strong_trustee_transcripts :
    ((fixture false).beforeTally.parameters.trusteeKeyProof.response.val,
      encode ((fixture false).decryptionProofs 0).commitment.1,
      encode ((fixture false).decryptionProofs 0).commitment.2,
      ((fixture false).decryptionProofs 0).response.val) = (6, 16, 6, 9) := by decide

/-- All first-candidate contributions are zero here, so the honest tally is zero,
ruling out an implementation that always returns one after attack rejection. -/
theorem repaired_tally_not_constant :
    let a := strongHonestBallot hashes.ballot 1 3 false aliceCoins
    let b := strongHonestBallot hashes.ballot 1 3 false bobCoins
    let first := repairedSubmit hashes.ballot 1 3 0 [] a
    let second := repairedSubmit hashes.ballot 1 3 1 first.2 b
    second.1 = .accepted ∧
      decryptWithPartial (boardTally second.2 0) (partialDecrypt (3 : Scalar) (boardTally second.2 0)) = 0 := by
  decide

/-- Strong statement hashing does not by itself stop the known aggregate reuse. -/
theorem strong_hash_alone_does_not_block_copy :
    let a := strongHonestBallot hashes.ballot 1 3 false aliceCoins
    let b := strongHonestBallot hashes.ballot 1 3 true bobCoins
    let attack := strongProofReuse hashes.ballot 1 3 1 1 1 a
    attack.StrongValid hashes.ballot 1 3 ∧ attack.FreshFor [a, b] ∧
      ¬ attack.ExpandedFreshFor [a, b] := by decide

def oldWeakProof : Proof01 Scalar Scalar := proveOne (fun _ => 5) 1 3 2 4 2 3

theorem literal_rerandomization_preserves_weak_proof :
    (oldWeakProof.rerandomize 1).Valid (fun _ => 5) 1 3
      (rerandomizeCiphertext (F := Scalar) 1 3 1 (encryptWith (F := Scalar) 1 3 2 1)) ∧
    (oldWeakProof.rerandomize 1).zero.response.val = 5 ∧
    (oldWeakProof.rerandomize 1).one.response.val = 2 ∧
    (encode (rerandomizeCiphertext (F := Scalar) 1 3 1 (encryptWith (F := Scalar) 1 3 2 1)).1,
      encode (rerandomizeCiphertext (F := Scalar) 1 3 1 (encryptWith (F := Scalar) 1 3 2 1)).2) = (8, 12) := by decide

theorem unchanged_responses_reject_rerandomization :
    ¬ oldWeakProof.Valid (fun _ => 5) 1 3 (encryptWith (F := Scalar) 1 3 3 1) := by decide

theorem statement_binding_rejects_same_rerandomization :
    let ct := encryptWith (F := Scalar) (1 : Scalar) 3 2 1
    let proof := strongProveVote hashes.ballot 1 3 true 2 4 2 3
    proof.StrongValid hashes.ballot 1 3 ct ∧
      ¬ (proof.rerandomize 1).StrongValid hashes.ballot 1 3 (rerandomizeCiphertext (F := Scalar) 1 3 1 ct) := by decide

#print axioms honest_valid_attack_rejected_and_tally_preserved
#print axioms literal_repaired_tally_and_share
#print axioms literal_strong_trustee_transcripts
#print axioms repaired_tally_not_constant
#print axioms strong_hash_alone_does_not_block_copy
#print axioms literal_rerandomization_preserves_weak_proof
#print axioms unchanged_responses_reject_rerandomization
#print axioms statement_binding_rejects_same_rerandomization

end ExplainableCrypto.Helios.Computational.RepairControls
