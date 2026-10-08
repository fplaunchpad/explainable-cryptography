import ExplainableCrypto.Helios.Computational.BallotJointReplayTape
import ExplainableCrypto.Helios.Computational.RepairedFiniteProgrammed
import ExplainableCrypto.Helios.Computational.RepairedSubmissionCost

/-! The actual repaired extractor saves a finite tagged tape, using the finite
shadow source. Existing joint extraction is recovered exactly. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]

noncomputable def repairedSubmissionTape_extract (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat) :
    OracleComp (FiatShamir.Fork.wrappedSpec F)
      (Option (RepairedSubmissionResult F G × (Option (Fin 2) → BallotWitness F))) :=
  ballotJointReplayTape (repairedSubmissionFiniteSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15)

attribute [local irreducible] repairedSubmissionSourceOracle repairedSubmissionFiniteSourceOracle

/-- Actual original submission and all three extracted witnesses have exactly
the existing joint distribution, including failure and rejected executions. -/
theorem repairedSubmissionTape_extract_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat) :
    repairedSubmissionTape_extract g pk vote attacker n =
      repairedSubmission_joint_extract g pk vote attacker n := by
  unfold repairedSubmissionTape_extract repairedSubmission_joint_extract
  rw [ballotJointReplayTape_eq,repairedSubmissionFiniteSource_eq]

/-- The actual saved tape has at most 4(m+19) events. Sampler cost remains explicit;
this is an entry bound, not a polynomial bit-time certificate. -/
theorem repairedSubmissionTape_saved_length_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (m : Nat)
    (hc : (uniformSample F).IsTotalQueryBound 1)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m)
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor)
    (ht : tape ∈ support (ballotReplayCollectTape (ballotReplaySourceRun
      (repairedSubmissionFiniteSourceOracle g pk vote attacker)) :
      OracleComp (FiatShamir.Fork.wrappedSpec F) _)) : tape.length ≤ 4*(m+19) := by
  apply ballotJointReplayTape_saved_length_le _ (4*(m+19)) _ tape ht
  rw [repairedSubmissionFiniteSource_eq]
  exact repairedSubmissionSource_total_query_bound g pk vote attacker m hc hb

/-- Canonical finite sampling discharges sampler cost in the existing interaction
bound for the tape-based actual extractor. Local decoding is still uncharged. -/
theorem repairedSubmissionTape_canonical_total_bound (g pk : G) (vote : Bool) :
    letI := SampleableType.ofFintype F
    ∀ (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n m : Nat),
    (∀ view, (attacker view).IsTotalQueryBound m) →
    (repairedSubmissionTape_extract g pk vote attacker n).IsTotalQueryBound (16*(m+19)) := by
  let := SampleableType.ofFintype F
  intro attacker n m hb
  rw [repairedSubmissionTape_extract_eq]
  exact repairedSubmission_joint_extract_canonical_total_bound g pk vote attacker n m hb

#print axioms repairedSubmissionTape_extract_eq
#print axioms repairedSubmissionTape_saved_length_le
#print axioms repairedSubmissionTape_canonical_total_bound
end ExplainableCrypto.Helios.Computational
