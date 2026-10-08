import ExplainableCrypto.Helios.Computational.BallotFiniteProgrammed
import ExplainableCrypto.Helios.Computational.RepairedFiniteCache

/-! The repaired submission source with finite internal shadow state, and its
complete execution with both caches finite. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]

noncomputable def repairedSubmissionFiniteSourceOracle (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    BallotOracleComp F G (RepairedSubmissionResult F G) :=
  Prod.fst <$> (simulateQ (ballotFiniteProgrammedImpl g pk)
    (repairedSubmissionOracle g pk vote attacker)).run .empty

/-- Exact raw source equality allows the existing replay and probability results
to use the finite shadow representation without a new correspondence premise. -/
theorem repairedSubmissionFiniteSource_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    repairedSubmissionFiniteSourceOracle g pk vote attacker =
      repairedSubmissionSourceOracle g pk vote attacker := by
  unfold repairedSubmissionFiniteSourceOracle repairedSubmissionSourceOracle
  have h := congrArg (fun p => Prod.fst <$> p) (runBallotFiniteProgrammed_eq g pk
    (repairedSubmissionOracle g pk vote attacker) .empty)
  simpa only [Functor.map_map,Function.comp_def,Prod.map_fst,id_eq,
    BallotFiniteProgrammedState.denote_empty] using h

/-- The complete repaired source preserves all decisions and boards, both caches,
the sticky flag and the ordered list of honest proof requests. -/
theorem repairedSubmissionFiniteProgrammed_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    (fun out => ((out.1.1,out.1.2.denote),out.2.denote)) <$>
      runBallotFiniteProgrammed g pk (repairedSubmissionOracle g pk vote attacker) =
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker) :=
  runBallotFiniteProgrammed_runtime g pk _

attribute [local irreducible] repairedSubmissionSourceOracle repairedSubmissionFiniteSourceOracle

/-- Live storage remains bounded for the source whose shadow cache is also finite. -/
theorem repairedSubmissionFiniteSource_length_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (out : RepairedSubmissionResult F G × BallotFiniteCache F G)
    (ho : out ∈ support (runBallotFiniteCache
      (repairedSubmissionFiniteSourceOracle g pk vote attacker) ∅)) :
    out.2.entries.length ≤ n+15 := by
  rw [repairedSubmissionFiniteSource_eq] at ho
  exact repairedSubmissionFiniteCache_length_le g pk vote attacker n hb out ho

#print axioms repairedSubmissionFiniteSource_eq
#print axioms repairedSubmissionFiniteProgrammed_eq
#print axioms repairedSubmissionFiniteSource_length_le
end ExplainableCrypto.Helios.Computational
