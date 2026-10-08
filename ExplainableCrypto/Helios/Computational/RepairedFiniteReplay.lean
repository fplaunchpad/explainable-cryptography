import ExplainableCrypto.Helios.Computational.BallotFiniteReplay
import ExplainableCrypto.Helios.Computational.RepairedReplayTape

/-! Actual repaired joint extraction with finite shadow and replay logging
caches, finite miss logs and finite saved tapes. Continuations remain OracleComp. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]

noncomputable def repairedSubmissionFinite_extract (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat) :
    OracleComp (FiatShamir.Fork.wrappedSpec F)
      (Option (RepairedSubmissionResult F G × (Option (Fin 2) → BallotWitness F))) :=
  ballotFiniteJointReplay (repairedSubmissionFiniteSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15)

attribute [local irreducible] repairedSubmissionSourceOracle repairedSubmissionFiniteSourceOracle

/-- Exact existing extraction, with finite logging in the first run and every
residual replay. Output, witnesses, rejection, collisions and randomness remain. -/
theorem repairedSubmissionFinite_extract_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat) :
    repairedSubmissionFinite_extract g pk vote attacker n =
      repairedSubmission_joint_extract g pk vote attacker n := by
  unfold repairedSubmissionFinite_extract repairedSubmission_joint_extract
  rw [ballotFiniteJointReplay_eq,repairedSubmissionFiniteSource_eq]

/-- The actual finite source logs at most n+15 hash misses. -/
theorem repairedSubmissionFinite_log_length_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (out : RepairedSubmissionResult F G × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionFiniteSourceOracle g pk vote attacker) (∅,[]))) :
    out.2.2.length ≤ n+15 := by
  have hsrc := repairedSubmissionTargetOracle_query_bound g pk vote attacker none n hb
  rw [← repairedSubmissionSource_select_eq,isQueryBoundP_map_iff] at hsrc
  have hf : (repairedSubmissionFiniteSourceOracle g pk vote attacker).IsQueryBoundP
      (isBallotHashQuery (F := F)) (n+15) := by
    rw [repairedSubmissionFiniteSource_eq]
    exact hsrc
  simpa only [List.length_nil,Nat.zero_add] using
    runBallotFiniteLogged_log_length_le _ (n+15) hf (∅,[]) out ho

/-- Finite logging preserves the established canonical total-interaction bound;
this still leaves local operations and typed continuation execution uncharged. -/
theorem repairedSubmissionFinite_canonical_total_bound (g pk : G) (vote : Bool) :
    letI := SampleableType.ofFintype F
    ∀ (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n m : Nat),
    (∀ view, (attacker view).IsTotalQueryBound m) →
    (repairedSubmissionFinite_extract g pk vote attacker n).IsTotalQueryBound (16*(m+19)) := by
  let := SampleableType.ofFintype F
  intro attacker n m hb
  rw [repairedSubmissionFinite_extract_eq]
  exact repairedSubmission_joint_extract_canonical_total_bound g pk vote attacker n m hb

#print axioms repairedSubmissionFinite_extract_eq
#print axioms repairedSubmissionFinite_log_length_le
#print axioms repairedSubmissionFinite_canonical_total_bound
end ExplainableCrypto.Helios.Computational
