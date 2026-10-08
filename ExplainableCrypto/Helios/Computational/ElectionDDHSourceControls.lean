import ExplainableCrypto.Helios.Computational.ElectionDDHSource
import ExplainableCrypto.Helios.Computational.StrongBallotOracleControls

/-! Full-state source and rejection controls. Small-field transcripts are the
independent multiplicative p=23/q=11 fixture, not a hardness instance. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSourceControls
open OracleComp OracleSpec ElectionDDHSource StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

/-- The source identity permits nonempty prior caches, flags and records. -/
theorem real_pair_after_cache :
    let s : BallotProgrammedState Scalar Scalar := ⟨cached 6,true,[stmt]⟩
    runBallotOracle ((honestPair (1 : Scalar) 3
      (ElectionDDHConstruction.paired (F := Scalar) 1 3 1 3 5 2 5 false).1).run s) (cached 6) =
    runBallotOracle ((simulateQ (ballotProgrammedImpl 1 3)
      (withNonces 1 3 false ((1 : Scalar),2) (4,5))).run s) (cached 6) := by
  have h := honest_pair_real (1 : Scalar) 3 false ((1 : Scalar),2) (4,5)
  simpa only [Prod.fst,Prod.snd,one_smul,show (1 + 4 : Scalar) = 5 from by decide +kernel] using congrArg (fun step => runBallotOracle
    (step.run (⟨cached 6,true,[stmt]⟩ : BallotProgrammedState Scalar Scalar)) (cached 6)) h

/-- Forgetting the retained sums preserves the original sampled query tree. -/
theorem projection_preserves_sampled_source :
    Prod.fst <$> sampledWithSums (F := Scalar) (G := Scalar) 1 3 false =
      repairedCastHonestPairOracle (F := Scalar) (G := Scalar) 1 3 false :=
  sampledWithSums_fst (F := Scalar) (G := Scalar) 1 3 false

def initial : ElectionProgrammedSource.State Scalar Scalar :=
  ⟨(∅ : ElectionOracle.Cache Scalar Scalar).cacheQuery (.key 1 3 4) 5,true,[stmt]⟩

/-- Full-cache statistical comparison after a real auxiliary cache entry. -/
theorem full_loss_after_key_query :
    tvDist (ElectionProgrammedSource.evaluate
      (ElectionProgrammedSource.ballots (F := Scalar) 1 3 false) initial ∅)
      ((fun out => ((out.1.1.1,out.1.2),out.2)) <$>
        (do let x ← uniformSample Scalar; let a ← uniformSample Scalar
            let t ← uniformSample Scalar; let b ← uniformSample Scalar
            ElectionProgrammedSource.evaluate
              (ballots (F := Scalar) 1 3 (x • (1 : Scalar)) (x • (3 : Scalar)) t a b false) initial ∅)) ≤
      4 / 11 := by
  have h := ballots_real_distance_le (F := Scalar) 1 3 false initial ∅
  norm_num at h ⊢
  exact h

/-- The explicit-statement step can return a conflicting proof, while preserving
its old cache answer and setting the private collision flag. -/
theorem conflicting_statement_reachable :
    ((proof,(⟨cached 6,true,[stmt]⟩ : BallotProgrammedState Scalar Scalar)),cached 6) ∈ support
      (runBallotOracle ((ballotProgrammedStatement (F := Scalar) stmt).run
        ⟨cached 6,false,[]⟩) (cached 6)) := by
  rw [ballotProgrammedStatement_runtime,support_map]
  refine ⟨((proof,true),cached 6),conflicting_simulation_flagged_and_preserved,?_⟩
  rfl

def invalidBallot : Ballot Scalar Scalar 2 :=
  ⟨![stmt.ciphertext,(0,0)],![proof,proof],proof⟩

/-- Actual verification rejects before freshness, retaining the incoming board.
The remaining two proofs need not be valid. -/
theorem conflicting_first_proof_rejects (board : List (BoardEntry Scalar Scalar)) :
    runBallotOracle (repairedSubmitOracle 1 3 0 board invalidBallot) (cached 6) =
      pure ((.invalidProof,board),cached 6) := by
  rw [repairedSubmitOracle,runBallotOracle_bind]
  have hv : runBallotOracle (strongBallotVerifyAllOracle 1 3 invalidBallot) (cached 6) =
      pure (false,cached 6) := by
    rw [strongBallotVerifyAllOracle,runBallotOracle_bind]
    have he : invalidBallot.coveredStatement 1 3 (some 0) = stmt := by decide +kernel
    rw [he,show invalidBallot.proof 0 = proof from rfl,conflicting_proof_rejected]
    simp [runBallotOracle]
  rw [hv]
  simp [runBallotOracle]

/-- Conditioning the comparison on an initially empty record would lose this
allowed incoming state; a true incoming flag is not reset by initialization. -/
theorem initial_is_not_empty :
    initial.cache (.key 1 3 4) = some 5 ∧ initial.bad = true ∧ initial.programmed ≠ [] := by
  decide +kernel

#print axioms real_pair_after_cache
#print axioms projection_preserves_sampled_source
#print axioms full_loss_after_key_query
#print axioms conflicting_statement_reachable
#print axioms conflicting_first_proof_rejects
#print axioms initial_is_not_empty
end ExplainableCrypto.Helios.Computational.ElectionDDHSourceControls
