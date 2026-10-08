import ExplainableCrypto.Helios.Computational.BallotReplayStorage
import ExplainableCrypto.Helios.Computational.BallotKeyRecord
import ExplainableCrypto.Helios.Computational.RepairedFiniteReplay

/-! Derived cache, log and element-record bounds for the actual finite source.
These are record counts, not bit lengths, peak memory or execution times. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
attribute [local irreducible] repairedSubmissionFiniteSourceOracle

/-- The actual finite replay cache and miss log have the same derived size,
with at most n+15 entries each from the per-view attacker hash bound. -/
theorem repairedSubmissionFinite_storage_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (out : RepairedSubmissionResult F G × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionFiniteSourceOracle g pk vote attacker) (∅,[]))) :
    out.2.1.entries.length = out.2.2.length ∧ out.2.1.entries.length ≤ n+15 ∧
      out.2.2.length ≤ n+15 := by
  have he := runBallotFiniteLogged_empty_sizes _ out ho
  have hl := repairedSubmissionFinite_log_length_le g pk vote attacker n hb out ho
  exact ⟨he,he ▸ hl,hl⟩

/-- The cache/log key records contain at most 16(n+15) group elements and
n+15 scalar answers. The eight full-key fields and cache/log counts are derived. -/
theorem repairedSubmissionFinite_record_cells_le (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (out : RepairedSubmissionResult F G × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionFiniteSourceOracle g pk vote attacker) (∅,[]))) :
    (ballotLoggedGroupRecord out.2).length ≤ 16*(n+15) ∧
      (ballotLoggedScalarRecord out.2).length ≤ n+15 := by
  obtain ⟨he,hc,hl⟩ := repairedSubmissionFinite_storage_le g pk vote attacker n hb out ho
  rw [ballotLoggedGroupRecord_length,ballotLoggedScalarRecord_length]
  constructor
  · omega
  · exact hc

#print axioms repairedSubmissionFinite_storage_le
#print axioms repairedSubmissionFinite_record_cells_le
end ExplainableCrypto.Helios.Computational
