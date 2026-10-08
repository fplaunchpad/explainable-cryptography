import ExplainableCrypto.Helios.Computational.RepairedSubmissionCost
import ExplainableCrypto.Helios.Computational.BallotReplayCostControls

/-! Canonical sampling discharges the actual source cost. Uniformity alone
allows padded samplers, and simulated proofs use four scalar draws. -/
namespace ExplainableCrypto.Helios.Computational.RepairedSubmissionCostControls
open OracleComp OracleSpec StrongBallotOracleControls BallotReplayCostControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
attribute [local irreducible] repairedSubmission_joint_extract repairedSubmissionSourceOracle

/-- Instantiate the actual repaired joint extractor with a zero-query attacker.
The bound covers any returned ballot and every rejection branch. -/
theorem canonical_constant_attacker_bound (b : Ballot Scalar Scalar 2) :
    (repairedSubmission_joint_extract (1 : Scalar) 2 false (fun _ => pure b) 0).IsTotalQueryBound 304 := by
  exact repairedSubmission_joint_extract_canonical_total_bound (F := Scalar) (G := Scalar) 1 2 false (fun _ => pure b) 0 0
    (fun _ => trivial)

def paddedCoin : ProbComp (Fin 2) := do
  let _ ← oneCoin
  oneCoin

/-- The padded algorithm is uniform even though it performs an extra draw. -/
@[instance_reducible] def paddedCoinSampler : SampleableType (Fin 2) where
  selectElem := paddedCoin
  mem_support_selectElem x := by simp [paddedCoin,oneCoin]
  probOutput_selectElem_eq x y := by simp [paddedCoin,oneCoin]

/-- A valid uniform sampler need not have the canonical one-query cost. -/
theorem uniform_sampler_cost_counterexample :
    letI := paddedCoinSampler
    ¬ (uniformSample (Fin 2)).IsTotalQueryBound 1 := by
  intro h
  exact Nat.not_lt_zero _ (h.2 0).1

/-- A simulated ballot proof performs four scalar draws; charging one is false. -/
theorem simulated_proof_not_one_query :
    ¬ ((strongBallotSimOracle (F := Scalar) stmt).run ∅).IsTotalQueryBound 1 := by
  intro h
  exact Nat.not_lt_zero _ (h.2 0).1

#print axioms canonical_constant_attacker_bound
#print axioms uniform_sampler_cost_counterexample
#print axioms simulated_proof_not_one_query
end ExplainableCrypto.Helios.Computational.RepairedSubmissionCostControls
