import ExplainableCrypto.Helios.Computational.ElectionDDHExtractedFinish
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls

/-! Directed share controls and an actual querying complete-game instance.
The field is a finite fixture, not a cryptographic hardness instance. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHExtractedFinishControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

private def nonces : Option (Fin 2) → BallotWitness Scalar :=
  fun i => (false,match i with | none => 15 | some i => if i = 0 then 6 else 9)

/-- These are arithmetic fixtures; their arbitrary unused records are not
asserted to be reachable prefix states. -/
theorem accepted_shares (out : PrefixResult Scalar Scalar Unit Unit) :
    extractedShares 3 {out with known := ![5,7],cast := (.accepted,[])} (some nonces) 0 = 33 ∧
    extractedShares 3 {out with known := ![5,7],cast := (.accepted,[])} (some nonces) 1 = 48 := by
  norm_num [extractedShares,nonces,smul_eq_mul]

/-- Rejection discards even a supplied nonce; both rejection reasons agree. -/
theorem rejected_shares (out : PrefixResult Scalar Scalar Unit Unit) :
    extractedShares 3 {out with known := ![5,7],cast := (.invalidProof,[])} (some nonces) 0 = 15 ∧
    extractedShares 3 {out with known := ![5,7],cast := (.reusedCiphertext,[])} (some nonces) 1 = 21 := by
  norm_num [extractedShares,smul_eq_mul]
  decide +kernel

/-- Missing extraction is an explicit fallback, which differs from the
correct accepted share. It must remain a charged failure event. -/
theorem missing_witness_differs (out : PrefixResult Scalar Scalar Unit Unit) :
    extractedShares 3 {out with known := ![5,7],cast := (.accepted,[])} none 0 = 15 ∧
    extractedShares 3 {out with known := ![5,7],cast := (.accepted,[])} none 0 ≠ 33 := by
  norm_num [extractedShares,smul_eq_mul]
  decide +kernel

/-- If only the first honest ciphertext survives, the pair's recorded nonce
sum cannot be used for its share. This excludes dropping honest acceptance. -/
theorem rejected_honest_sum_differs :
    partialDecrypt (3 : Scalar) ((1,3) : Ciphertext Scalar) = 3 ∧
    (5 : Scalar) • (3 : Scalar) ≠ partialDecrypt (3 : Scalar) ((1,3) : Ciphertext Scalar) := by
  decide +kernel

private theorem prepare_bound : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := Scalar)) 1 := by
  simp [prepare,ask,key,ElectionQueryBound.isBallot]

private theorem cast_bound (b : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b remembered).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := Scalar)) 0 := by
  simp [adversary,ask,key,ElectionQueryBound.isBallot]

/-- Full prepared/cast/guess behavior and final caches appear in the bound.
The non-DH challenge also exercises cancellation outside the real DDH world. -/
theorem finish_after_queries (b : Ballot Scalar Scalar 2) (k : Nat) (δ : ENNReal) :
    ENNReal.ofReal (tvDist
      (extractedGame (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b) 10 k)
      (ElectionProgrammedSource.evaluate
        (completedReal (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 3 prepare (adversary b)) .empty ∅)) ≤
      Pr[fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted) |
        runBallotOracle (prefixSource (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b)) ∅] +
        (33*δ + (1-(δ-1/257)^3)^k) := by
  have h := extracted_finish_distance_le (fun p => p.trusteeKeyProof.response.val) 1 2 7
    (by decide +kernel : (1 : Scalar) ≠ 0) 3 prepare (adversary b) 1 0 k prepare_bound (cast_bound b) δ
  norm_num [smul_eq_mul] at h ⊢
  exact h

#print axioms accepted_shares
#print axioms rejected_shares
#print axioms missing_witness_differs
#print axioms rejected_honest_sum_differs
#print axioms finish_after_queries
end ExplainableCrypto.Helios.Computational.ElectionDDHExtractedFinishControls
