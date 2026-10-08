import ExplainableCrypto.Helios.Computational.BallotFiniteCache
import ExplainableCrypto.Helios.Computational.RepairedSubmissionSource

/-! The finite live-cache interpreter executes the actual repaired submission
source. Its internal programmed shadow state is still the semantic representation. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
attribute [local irreducible] repairedSubmissionSourceOracle

/-- The finite live cache preserves the complete actual original submission,
all original decisions and its final semantic live cache. -/
theorem repairedSubmissionFiniteCache_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    (fun out => (out.1,out.2.denote)) <$>
      runBallotFiniteCache (repairedSubmissionSourceOracle g pk vote attacker) ∅ =
    (fun out => (out.1.1,out.2)) <$>
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker) := by
  rw [runBallotFiniteCache_eq,BallotFiniteCache.denote_empty,repairedSubmissionSource_runtime]

/-- Actual supported finite executions need at most n+15 stored live entries;
the source query budget and initial empty cover are derived. -/
theorem repairedSubmissionFiniteCache_length_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (out : RepairedSubmissionResult F G × BallotFiniteCache F G)
    (ho : out ∈ support (runBallotFiniteCache (repairedSubmissionSourceOracle g pk vote attacker) ∅)) :
    out.2.entries.length ≤ n+15 := by
  have ht := repairedSubmissionTargetOracle_query_bound g pk vote attacker none n hb
  rw [← repairedSubmissionSource_select_eq,isQueryBoundP_map_iff] at ht
  simpa only [AList.empty_entries,List.length_nil,Nat.zero_add] using
    runBallotFiniteCache_length_le (repairedSubmissionSourceOracle g pk vote attacker) (n+15) ht ∅ out ho

#print axioms repairedSubmissionFiniteCache_eq
#print axioms repairedSubmissionFiniteCache_length_le
end ExplainableCrypto.Helios.Computational
