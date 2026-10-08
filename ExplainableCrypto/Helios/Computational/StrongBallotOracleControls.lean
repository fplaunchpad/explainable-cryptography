import ExplainableCrypto.Helios.Computational.StrongBallotSimulator
import ExplainableCrypto.Helios.Computational.ExecutionControls

/-! Literal multiplicative p=23/q=11 and conflicting-cache controls. The Python
oracle derives these commitments without using the Lean group representation. -/
namespace ExplainableCrypto.Helios.Computational.StrongBallotOracleControls

open OracleComp OracleSpec
abbrev Scalar := ZMod 11
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def stmt : BallotStatement Scalar := ⟨1,3,(3,9)⟩
def pc : BallotCommitment Scalar := ballotSimCommit stmt (5 : Scalar) (2,3,4)
def proof : Proof01 Scalar Scalar := ballotTranscriptProof pc 5 (2,3,4)
def transcript : BallotCommitment Scalar × Scalar × BallotResponse Scalar := (pc,5,(2,3,4))
def cached (c : Scalar) : BallotOracleCache Scalar Scalar :=
  (∅ : BallotOracleCache Scalar Scalar).cacheQuery (stmt,pc) c

theorem literal_simulated_commitments :
    ((ExecutionControls.encode pc.1.1, ExecutionControls.encode pc.1.2),
      (ExecutionControls.encode pc.2.1, ExecutionControls.encode pc.2.2)) = ((3,4),(18,12)) := by decide

private theorem transcript_supported :
    transcript ∈ support (ballotFullSimTranscript (F := Scalar) stmt) := by
  simp only [ballotFullSimTranscript, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff]
  exact ⟨5, by simp, 2, by simp, 3, by simp, 4, by simp, rfl⟩

theorem fresh_simulation_possible :
    ((proof,false),cached 5) ∈ support ((strongBallotSimOracle (F := Scalar) stmt).run ∅) := by
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion]
  refine ⟨transcript, transcript_supported, ?_⟩
  simp [transcript, cached, proof]

theorem fresh_simulation_verifies :
    runBallotOracle (strongBallotVerifyOracle stmt proof) (cached 5) = pure (true,cached 5) :=
  strongBallotSimOracle_unflagged_valid stmt ∅ _ fresh_simulation_possible rfl

theorem conflicting_simulation_flagged_and_preserved :
    ((proof,true),cached 6) ∈ support ((strongBallotSimOracle (F := Scalar) stmt).run (cached 6)) := by
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion]
  refine ⟨transcript, transcript_supported, ?_⟩
  simp [transcript, cached, proof]

theorem conflicting_proof_rejected :
    runBallotOracle (strongBallotVerifyOracle stmt proof) (cached 6) = pure (false,cached 6) := by
  rw [runBallotOracle_verify_cached stmt proof (cached 6) 6 (by
    simp [cached, proof, Proof01.commitment, ballotTranscriptProof])]
  congr 1

/-- A statement change keeps the commitments but names a distinct strong-hash query. -/
theorem statement_not_discarded_from_hash_key :
    (stmt,pc) ≠ ({stmt with ciphertext := (3,10)},pc) ∧
    pc = (proof.commitment) := by decide

#print axioms literal_simulated_commitments
#print axioms fresh_simulation_possible
#print axioms fresh_simulation_verifies
#print axioms conflicting_simulation_flagged_and_preserved
#print axioms conflicting_proof_rejected
#print axioms statement_not_discarded_from_hash_key

end ExplainableCrypto.Helios.Computational.StrongBallotOracleControls
