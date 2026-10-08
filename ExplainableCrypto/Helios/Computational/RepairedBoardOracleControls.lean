import ExplainableCrypto.Helios.Computational.HonestPrefixOracle
import ExplainableCrypto.Helios.Computational.BallotProofProvenanceControls

/-! Full-proof oracle decision controls using independently derived p=23/q=11
ballots. The preloaded cache is a deterministic verifier fixture, not a claim
of empty-cache reachability. Historical rejection remains observable. -/
namespace ExplainableCrypto.Helios.Computational.RepairedBoardOracleControls
open OracleComp OracleSpec
open RepairControls (Scalar hashes)
open ExecutionControls (aliceCoins bobCoins)
open BallotProofProvenanceControls (acceptedPrefix rejectedPrefix thirdCoins rejectedBobCoins crossKindCoins)
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

local instance (hash : Hash Scalar Scalar) (g pk : Scalar) (ct : Ciphertext Scalar)
    (p : Proof01 Scalar Scalar) : Decidable (p.Valid hash g pk ct) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance
local instance (hash : StatementHash Scalar Scalar) (g pk : Scalar) (ct : Ciphertext Scalar)
    (p : Proof01 Scalar Scalar) : Decidable (p.StrongValid hash g pk ct) := by
  unfold Proof01.StrongValid
  infer_instance

def cache : BallotOracleCache Scalar Scalar := fun key =>
  some (hashes.ballot key.1.generator key.1.publicKey key.1.ciphertext key.2)
def fresh := strongHonestBallot hashes.ballot (1 : Scalar) 3 false thirdCoins
def reused := strongHonestBallot hashes.ballot (1 : Scalar) 3 false crossKindCoins
def badAggregate (b : Ballot Scalar Scalar 2) : Ballot Scalar Scalar 2 :=
  {b with overall := {b.overall with one := {b.overall.one with challenge := b.overall.one.challenge + 1}}}

private theorem fixture_verify (b : Ballot Scalar Scalar 2) (i : Option (Fin 2)) :
    runBallotOracle (strongBallotVerifyOracle (b.coveredStatement 1 3 i) (b.coveredProof i)) cache =
      pure (decide ((b.coveredProof i).StrongValid hashes.ballot 1 3 (b.coveredCiphertext i)),cache) := by
  rw [runBallotOracle_verify_cached _ _ cache _ rfl]
  rfl

private theorem fixture_all (b : Ballot Scalar Scalar 2) :
    runBallotOracle (strongBallotVerifyAllOracle 1 3 b) cache =
      pure (decide (b.StrongValid hashes.ballot 1 3),cache) := by
  have h0 := fixture_verify b (some 0)
  have h1 := fixture_verify b (some 1)
  have ht := fixture_verify b none
  simp only [Ballot.coveredProof,Ballot.coveredCiphertext] at h0 h1 ht
  rw [strongBallotVerifyAllOracle,runBallotOracle_bind,h0]
  simp only [pure_bind]
  by_cases hv0 : (b.proof 0).StrongValid hashes.ballot 1 3 (b.ciphertext 0)
  · simp only [hv0,decide_true,Bool.not_true,Bool.false_eq_true,if_false]
    rw [runBallotOracle_bind,h1]
    simp only [pure_bind]
    by_cases hv1 : (b.proof 1).StrongValid hashes.ballot 1 3 (b.ciphertext 1)
    · simp only [hv1,decide_true,Bool.not_true,Bool.false_eq_true,if_false]
      rw [ht]
      simp only [Ballot.StrongValid,Fin.forall_fin_two,hv0,hv1,and_self,true_and]
      congr 1
    · simp [hv1,runBallotOracle,Ballot.StrongValid,Fin.forall_fin_two]
  · simp [hv0,runBallotOracle,Ballot.StrongValid,Fin.forall_fin_two]

private theorem fixture_submit (b : Ballot Scalar Scalar 2) :
    runBallotOracle (repairedSubmitOracle 1 3 2 acceptedPrefix.2 b) cache =
      pure (repairedSubmit hashes.ballot 1 3 2 acceptedPrefix.2 b,cache) := by
  rw [repairedSubmitOracle,runBallotOracle_bind,fixture_all]
  by_cases hv : b.StrongValid hashes.ballot 1 3 <;>
    by_cases hf : b.ExpandedFreshFor (acceptedPrefix.2.map BoardEntry.ballot) <;>
    simp [hv,hf,repairedSubmit,runBallotOracle]

theorem fresh_full_ballot_accepted :
    runBallotOracle (repairedSubmitOracle 1 3 2 acceptedPrefix.2 fresh) cache =
      pure ((.accepted,acceptedPrefix.2 ++ [⟨2,fresh⟩]),cache) := by
  rw [fixture_submit]
  rfl

theorem valid_cross_kind_reuse_rejected :
    runBallotOracle (repairedSubmitOracle 1 3 2 acceptedPrefix.2 reused) cache =
      pure ((.reusedCiphertext,acceptedPrefix.2),cache) := by
  rw [fixture_submit]
  rfl

theorem invalid_reuse_proof_rejection_has_priority :
    runBallotOracle (repairedSubmitOracle 1 3 2 acceptedPrefix.2 (badAggregate reused)) cache =
      pure ((.invalidProof,acceptedPrefix.2),cache) := by
  rw [fixture_submit]
  rfl

theorem fresh_components_do_not_replace_aggregate_validation :
    (∀ i, ((badAggregate fresh).proof i).StrongValid hashes.ballot 1 3 (fresh.ciphertext i)) ∧
    (badAggregate fresh).ExpandedFreshFor (acceptedPrefix.2.map BoardEntry.ballot) ∧
    runBallotOracle (repairedSubmitOracle 1 3 2 acceptedPrefix.2 (badAggregate fresh)) cache =
      pure ((.invalidProof,acceptedPrefix.2),cache) := by
  refine ⟨by decide,by decide,?_⟩
  rw [fixture_submit]
  rfl

theorem prefix_function_keeps_honest_rejection :
    simulateQ (ballotFunctionImpl hashes.ballot)
      (repairedCastHonestPairWithCoinsOracle (1 : Scalar) 3 false aliceCoins rejectedBobCoins) =
      pure rejectedPrefix ∧ rejectedPrefix.1 = (.accepted,.reusedCiphertext) :=
  ⟨repairedCastHonestPairWithCoinsOracle_function _ _ _ _ _ _,by decide⟩

theorem prefix_function_accepts_separated_honest_ballots :
    simulateQ (ballotFunctionImpl hashes.ballot)
      (repairedCastHonestPairWithCoinsOracle (1 : Scalar) 3 false aliceCoins bobCoins) =
      pure acceptedPrefix ∧ acceptedPrefix.1 = (.accepted,.accepted) :=
  ⟨repairedCastHonestPairWithCoinsOracle_function _ _ _ _ _ _,by decide⟩

#print axioms fresh_full_ballot_accepted
#print axioms valid_cross_kind_reuse_rejected
#print axioms invalid_reuse_proof_rejection_has_priority
#print axioms fresh_components_do_not_replace_aggregate_validation
#print axioms prefix_function_keeps_honest_rejection
#print axioms prefix_function_accepts_separated_honest_ballots
end ExplainableCrypto.Helios.Computational.RepairedBoardOracleControls
