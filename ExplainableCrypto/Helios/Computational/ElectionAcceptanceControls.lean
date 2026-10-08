import ExplainableCrypto.Helios.Computational.ElectionExtractionBound
import ExplainableCrypto.Helios.Computational.ElectionReplayControls
import ExplainableCrypto.Helios.Computational.RepairedBoardOracleControls

/-! Independent preloaded verifier and mixed-query controls. The preloaded
fixture is not an empty-cache reachability or universal extraction-success claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionAcceptanceControls
open OracleComp OracleSpec ElectionOracle ElectionCache
open RepairControls (Scalar)
open RepairedBoardOracleControls (fresh cache)
open BallotProofProvenanceControls (acceptedPrefix)
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def fullCache : Cache Scalar Scalar := replace (fun _ => none) cache

/-- The independently checked fresh ballot remains valid after arbitrary full
proof-domain queries, including the attacker's later callback. -/
theorem late_queries_preserve_validity {A : Type} (oa : Comp Scalar Scalar A)
    (out : A × Cache Scalar Scalar) (ho : out ∈ support (run oa fullCache)) :
    fresh.CachedStrongValid 1 3 (project out.2) := by
  have hs : ((Decision.accepted,acceptedPrefix.2 ++ [⟨2,fresh⟩]),cache) ∈
      support (runBallotOracle (repairedSubmitOracle 1 3 2 acceptedPrefix.2 fresh) cache) := by
    rw [RepairedBoardOracleControls.fresh_full_ballot_accepted]
    simp
  have hv := (repairedSubmitOracle_accepted 1 3 2 acceptedPrefix.2 fresh cache _ hs rfl).1
  apply Ballot.CachedStrongValid.mono 1 3 fresh hv
  intro key c hc
  exact ElectionAcceptance.run_cache_le oa fullCache out ho (show fullCache (.ballot key.1 key.2) = some c from hc)

/-- Erasing the cache destroys the stored-challenge certificate for this ballot. -/
theorem erased_cache_not_valid : ¬ fresh.CachedStrongValid 1 3 (∅ : BallotOracleCache Scalar Scalar) := by
  intro hv
  obtain ⟨c,hc,_⟩ := hv none
  cases hc

/-- Five mixed requests contain two ballot requests, including the repeated hit.
The structural query bound counts requests, not only cache misses. -/
theorem mixed_two_ballot_queries :
    ElectionReplayControls.mixed.IsQueryBoundP (ElectionQueryBound.isBallot (F := Scalar)) 2 := by
  simp [ElectionReplayControls.mixed,ask,ElectionQueryBound.isBallot,
    ElectionOracleControls.keyRequest,ElectionOracleControls.partialRequest]

theorem mixed_one_is_insufficient :
    ¬ ElectionReplayControls.mixed.IsQueryBoundP (ElectionQueryBound.isBallot (F := Scalar)) 1 := by
  simp [ElectionReplayControls.mixed,ask,ElectionQueryBound.isBallot,
    ElectionOracleControls.keyRequest,ElectionOracleControls.partialRequest]

/-- The bound's numerical expression need not truncate to zero. This checks
its arithmetic at acceptance one, not actual-election acceptance probability. -/
theorem numerical_bound_positive :
    0 < ((1 : ENNReal) - 3*16*(1/64)) * ((1/64) - (101 : ENNReal)⁻¹)^3 := by
  norm_num
  constructor
  · exact ENNReal.div_lt_of_lt_mul (by norm_num)
  · apply bot_lt_iff_ne_bot.mpr
    apply pow_ne_zero
    exact ne_of_gt (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_inv.mpr (by norm_num)))

#print axioms late_queries_preserve_validity
#print axioms erased_cache_not_valid
#print axioms mixed_two_ballot_queries
#print axioms mixed_one_is_insufficient
#print axioms numerical_bound_positive
end ExplainableCrypto.Helios.Computational.ElectionAcceptanceControls
