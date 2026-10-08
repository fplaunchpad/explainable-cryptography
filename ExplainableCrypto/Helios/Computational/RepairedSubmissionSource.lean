import ExplainableCrypto.Helios.Computational.RepairedSubmissionExtraction
import ExplainableCrypto.Helios.Computational.BallotForkSource

/-! The selected-proof extractor now returns its original complete submission.
This retains the first execution; it does not yet jointly extract three proofs. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]

noncomputable def repairedSubmissionSourceOracle (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    BallotOracleComp F G (RepairedSubmissionResult F G) :=
  Prod.fst <$> (simulateQ (ballotProgrammedImpl g pk)
    (repairedSubmissionOracle g pk vote attacker)).run .empty

def repairedSubmissionSelect (g pk : G) (i : Option (Fin 2))
    (out : RepairedSubmissionResult F G) : BallotStatement G × Proof01 F G :=
  (out.ballot.coveredStatement g pk i,
    if out.Accepted then out.ballot.coveredProof i else replayRejectedProof g)

/-- Exactly the old target computation, before erasing its source value. -/
theorem repairedSubmissionSource_select_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2)) :
    repairedSubmissionSelect g pk i <$> repairedSubmissionSourceOracle g pk vote attacker =
      repairedSubmissionTargetOracle g pk vote attacker i := by
  simp [repairedSubmissionSourceOracle,repairedSubmissionSelect,repairedSubmissionTargetOracle,
    map_eq_bind_pure_comp,bind_assoc]

/-- Source projection retains all actual public results and the live cache. -/
theorem repairedSubmissionSource_runtime (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    runBallotOracle (repairedSubmissionSourceOracle g pk vote attacker) ∅ =
      (fun out => (out.1.1,out.2)) <$>
        runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker) := by
  simp [repairedSubmissionSourceOracle,runBallotProgrammed,runBallotOracle,simulateQ_map,
    StateT.run_map]

noncomputable def repairedSubmission_extractSource (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (i : Option (Fin 2)) (n : Nat) :=
  ballotForkSourceExtract (repairedSubmissionSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk i) (n+15)

theorem repairedSubmission_extractSource_project (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (i : Option (Fin 2)) (n : Nat) :
    Option.map Prod.snd <$> repairedSubmission_extractSource g pk vote attacker i n =
      repairedSubmission_extract g pk vote attacker i n := by
  rw [repairedSubmission_extractSource,ballotForkSourceExtract_project,
    repairedSubmissionSource_select_eq]
  rfl

section Probability
local instance submissionSourceInhabited : Inhabited F := ⟨0⟩
noncomputable local instance submissionSourceUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Retaining the original submission introduces no extraction probability loss. -/
theorem repairedSubmission_extractSource_probability_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (i : Option (Fin 2)) (n : Nat) :
    Pr[fun out => out.isSome | repairedSubmission_extractSource g pk vote attacker i n] =
      Pr[fun out => out.isSome | repairedSubmission_extract g pk vote attacker i n] := by
  rw [← repairedSubmission_extractSource_project,probEvent_map]
  simp only [Function.comp_def,Option.isSome_map]

theorem repairedSubmission_extractSource_le (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (i : Option (Fin 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    let accepted := Pr[fun out => out.1.1.decision = .accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    let a := accepted - (9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ)))
    a * (a / (n+16 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun out => out.isSome | repairedSubmission_extractSource g pk vote attacker i n] := by
  rw [repairedSubmission_extractSource_probability_eq]
  exact repairedSubmission_extract_le g pk hg vote attacker i n hb
end Probability

attribute [local irreducible] repairedSubmissionSourceOracle

/-- The returned complete submission itself accepted, and the witness is for
its selected ciphertext. It is the first execution retained by the rich fork. -/
theorem repairedSubmission_extractSource_valid (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (i : Option (Fin 2)) (n : Nat) (result : RepairedSubmissionResult F G)
    (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (result,stmt,wit) ∈ support
      (repairedSubmission_extractSource g pk vote attacker i n)) :
    result.Accepted ∧ stmt.Witnesses wit ∧ stmt = result.ballot.coveredStatement g pk i ∧
      ∃ out ∈ support (runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)),
        out.1.1 = result := by
  have hs := ballotForkSourceExtract_valid (repairedSubmissionSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk i) (n+15) result stmt wit ho
  obtain ⟨hv,hstmt,⟨cache,hcache⟩,c,hproof⟩ := hs
  have ha : result.Accepted := by
    by_contra hn
    rw [hstmt] at hproof
    simp only [repairedSubmissionSelect,if_neg hn,Ballot.coveredStatement] at hproof
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hproof.1.1.symm)
  rw [repairedSubmissionSource_runtime,support_map] at hcache
  obtain ⟨out,hout,he⟩ := hcache
  exact ⟨ha,hv,hstmt,out,hout,congrArg Prod.fst he⟩

#print axioms repairedSubmissionSource_select_eq
#print axioms repairedSubmissionSource_runtime
#print axioms repairedSubmission_extractSource_project
#print axioms repairedSubmission_extractSource_probability_eq
#print axioms repairedSubmission_extractSource_le
#print axioms repairedSubmission_extractSource_valid
end ExplainableCrypto.Helios.Computational
