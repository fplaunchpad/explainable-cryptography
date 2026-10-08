import ExplainableCrypto.Helios.Computational.ElectionDDHParameters
import ExplainableCrypto.Helios.Computational.ElectionDDHSourceCostControls

/-! Parameter boundary controls and complete-game instantiations. Small fields
are arithmetic fixtures, not hardness instances. Large replay trees stay symbolic. -/
namespace ExplainableCrypto.Helios.Computational.BallotReplayParametersControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩

/-- A non-vacuous target; the large exponent is discharged by the general proof. -/
theorem positive_accuracy :
    3*(12:ENNReal)⁻¹ + (1-((12:ENNReal)⁻¹-(29:ENNReal)⁻¹)^3)^55296 ≤ (2:ENNReal)⁻¹ := by
  simpa only [ballotReplayTrials, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul,
    Nat.cast_zero, zero_add, mul_one, Nat.cast_ofNat,
    show (6:ENNReal)*2 = 12 by norm_num] using
    ballotReplay_parameters 0 29 2 (by decide) (by decide)

/-- Missing field size is a false claim: truncated success is zero, so the
failure remains one regardless of this large repetition count. -/
theorem field_size_required :
    ¬ (3*(12:ENNReal)⁻¹ + (1-((12:ENNReal)⁻¹-(2:ENNReal)⁻¹)^3)^55296 ≤ (2:ENNReal)⁻¹) := by
  have hi : (12:ENNReal)⁻¹ ≤ (2:ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (by norm_num)
  rw [tsub_eq_zero_of_le hi]
  simp only [zero_pow (by decide : 3 ≠ 0), tsub_zero, one_pow]
  intro h
  have h1 : (1:ENNReal) ≤ (2:ENNReal)⁻¹ := (le_add_left le_rfl).trans h
  norm_num at h1

/-- Zero accuracy input gives an infinite allowance, not meaningful secrecy. -/
theorem zero_accuracy_vacuous : (0:ENNReal)⁻¹ = ⊤ ∧ ballotReplayTrials 9 0 = 0 := by
  simp [ballotReplayTrials]

/-- Independent control: making no attempts leaves the full residual failure. -/
theorem zero_trials_fail :
    ¬ (3*(12:ENNReal)⁻¹ + (1-((12:ENNReal)⁻¹-(29:ENNReal)⁻¹)^3)^0 ≤ (2:ENNReal)⁻¹) := by
  simp only [pow_zero]
  intro h
  have h1 : (1:ENNReal) ≤ (2:ENNReal)⁻¹ := (le_add_left le_rfl).trans h
  norm_num at h1

private def quiet (b : Ballot Scalar Scalar 2) : Unit → Adversary Scalar Scalar Unit :=
  fun _ => ⟨fun _ => pure (b,()), fun _ _ => pure false⟩

/-- Actual complete non-DH input game with finite field 257: N=9, e=2 and
k=55,296,000. All honest/trustee/rejection observations are retained. -/
theorem complete_accuracy (b : Ballot Scalar Scalar 2) :
    ENNReal.ofReal (tvDist
      (extractedGame (fun p => p.trusteeKeyProof.response.val) 1 (3:Scalar) 2 7
        (pure ()) (quiet b) 9 (ballotReplayTrials 9 2))
      (ElectionProgrammedSource.evaluate
        (completedReal (fun p => p.trusteeKeyProof.response.val) 1 (3:Scalar) 2 7 3
          (pure ()) (quiet b)) .empty ∅)) ≤
      Pr[fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted) |
        runBallotOracle (prefixSource (fun p => p.trusteeKeyProof.response.val)
          1 (3:Scalar) 2 7 (pure ()) (quiet b)) ∅] + (2:ENNReal)⁻¹ := by
  simpa only [smul_eq_mul, mul_one, Nat.reduceAdd, Nat.cast_ofNat] using extracted_finish_accuracy
    (fun p => p.trusteeKeyProof.response.val) (1:Scalar) 2 7 (by decide +kernel)
    3 (pure ()) (quiet b) 0 0 2 (by trivial) (fun _ _ => by trivial)
    (by decide) (by norm_num [Scalar, ZMod.card])

/-- A querying adversary still uses the complete interaction budget, including
its auxiliary access and final guess, with the same computed repetition count. -/
theorem querying_cost (b : Ballot Scalar Scalar 2) :
    (extractedGame (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b)
      10 (ballotReplayTrials 10 2)).IsTotalQueryBound
        ((1+3*(3456*11^3*2^4))*90+8) :=
  ElectionDDHSourceCostControls.complete_after_queries b (ballotReplayTrials 10 2)

#print axioms positive_accuracy
#print axioms field_size_required
#print axioms zero_accuracy_vacuous
#print axioms zero_trials_fail
#print axioms complete_accuracy
#print axioms querying_cost
end ExplainableCrypto.Helios.Computational.BallotReplayParametersControls
