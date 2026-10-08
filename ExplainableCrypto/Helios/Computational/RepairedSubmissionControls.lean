import ExplainableCrypto.Helios.Computational.RepairedSubmissionExtraction
import ExplainableCrypto.Helios.Computational.RepairedBoardOracleControls

/-! Independent accepted/rejected board fixtures exercise replay selection.
The rejected prefix can be followed by an accepted valid ballot; using that
proof without the honest-prefix guard would count an excluded execution. -/
namespace ExplainableCrypto.Helios.Computational.RepairedSubmissionControls
open OracleComp OracleSpec
open RepairControls (Scalar hashes)
open BallotProofProvenanceControls (acceptedPrefix rejectedPrefix thirdCoins)
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

local instance (p : Proof01 Scalar Scalar) (c : Scalar) (ct : Ciphertext Scalar) :
    Decidable (p.Valid (fun _ => c) 1 3 ct) := by
  unfold Proof01.Valid Branch.Valid; infer_instance

def accepted : RepairedSubmissionResult Scalar Scalar :=
  let b := strongHonestBallot hashes.ballot 1 3 false thirdCoins
  ⟨acceptedPrefix,b,.accepted,acceptedPrefix.2 ++ [⟨2,b⟩]⟩

def rejected : RepairedSubmissionResult Scalar Scalar :=
  let b := strongHonestBallot hashes.ballot 1 3 true ExecutionControls.bobCoins
  ⟨rejectedPrefix,b,.accepted,rejectedPrefix.2 ++ [⟨2,b⟩]⟩

theorem accepted_full_challenges_retained :
    accepted.Accepted ∧ ∀ i, (if accepted.Accepted then accepted.ballot.coveredProof i
      else replayRejectedProof 1) = accepted.ballot.coveredProof i := by
  have h : accepted.Accepted := by decide
  simp [h]

theorem rejected_honest_prefix_still_has_accepted_submission :
    ¬ rejected.Accepted ∧ rejected.decision = .accepted ∧
    (repairedSubmit hashes.ballot 1 3 2 rejected.honest.2 rejected.ballot).1 = .accepted := by decide

theorem rejected_prefix_contributes_zero (cache : BallotOracleCache Scalar Scalar)
    (i : Option (Fin 2)) :
    Pr[fun out => out.1 | runBallotOracle
      (strongBallotVerifyOracle (rejected.ballot.coveredStatement 1 3 i)
        (if rejected.Accepted then rejected.ballot.coveredProof i else replayRejectedProof 1)) cache] = 0 := by
  rw [if_neg rejected_honest_prefix_still_has_accepted_submission.1]
  exact replayRejectedProof_verification_zero 1 3 (by decide) _ cache

/-- The very same excluded execution has a valid unchanged full proof in the
preloaded verifier fixture. Omitting the guard would count it as acceptance. -/
theorem valid_fallback_would_inflate :
    runBallotOracle (strongBallotVerifyOracle (rejected.ballot.coveredStatement 1 3 (some 0))
      (rejected.ballot.proof 0)) RepairedBoardOracleControls.cache =
      pure (true,RepairedBoardOracleControls.cache) := by
  rw [runBallotOracle_verify_cached (F := Scalar) (G := Scalar) _ _ RepairedBoardOracleControls.cache _ rfl]
  rfl

theorem rejected_proof_still_queries :
    let stmt : BallotStatement Scalar := ⟨1,3,(6,7)⟩
    let proof : Proof01 Scalar Scalar := replayRejectedProof 1
    (false,(∅ : BallotOracleCache Scalar Scalar).cacheQuery (stmt,proof.commitment) 5) ∈
      support (runBallotOracle (strongBallotVerifyOracle stmt proof) ∅) := by
  dsimp only
  rw [strongBallotVerifyOracle,runBallotOracle_bind,runBallotOracle_query]
  simp only [QueryCache.empty_apply,support_bind,Set.mem_iUnion]
  refine ⟨(5,(∅ : BallotOracleCache Scalar Scalar).cacheQuery (⟨1,3,(6,7)⟩,(replayRejectedProof (F := Scalar) (1 : Scalar)).commitment) 5),?_,?_⟩
  · simp
  · simp [runBallotOracle,replayRejectedProof,Proof01.Valid,Branch.Valid]

#print axioms accepted_full_challenges_retained
#print axioms rejected_honest_prefix_still_has_accepted_submission
#print axioms rejected_prefix_contributes_zero
#print axioms valid_fallback_would_inflate
#print axioms rejected_proof_still_queries
end ExplainableCrypto.Helios.Computational.RepairedSubmissionControls
