import ExplainableCrypto.Helios.Computational.ElectionDDHRejection
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls

/-! Actual rejection-game instances and independent probability controls.
The small field carries no DDH hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHRejectionControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩

private theorem prepare_bound : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 2 := by
  simp [prepare,ask,key,ElectionCacheBudget.isHash]

private theorem cast_bound (b : Ballot Scalar Scalar 2) (initial : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := Scalar)) 1 := by
  simp [adversary,ask,key,ElectionCacheBudget.isHash]

private theorem generator_injective : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
  intro a b h
  simpa [smul_eq_mul] using h

private theorem loss_coercion : ENNReal.ofReal (155/257 : ℝ) = 155/257 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The real bound is for the actual prepared prefix, including prior queries. -/
theorem real_after_queries (b : Ballot Scalar Scalar 2) :
    Pr[= true | DiffieHellman.ddhExpReal (1 : Scalar)
      (honestRejectDistinguisher (fun p => p.trusteeKeyProof.response.val) prepare (adversary b))] ≤
      9/256 + 155/257 := by
  have h := honestReject_real_le (fun p => p.trusteeKeyProof.response.val) 1 generator_injective
    prepare (adversary b) 2 1 prepare_bound (cast_bound b)
  norm_num [noncePointBound] at h
  rw [loss_coercion] at h
  simpa only [div_eq_mul_inv] using h

/-- Random rejection includes the actual public test's DDH advantage. -/
theorem random_after_queries (b : Ballot Scalar Scalar 2) :
    Pr[= true | DiffieHellman.ddhExpRand (1 : Scalar)
      (honestRejectDistinguisher (fun p => p.trusteeKeyProof.response.val) prepare (adversary b))] ≤
      (9/256 + 155/257) + ENNReal.ofReal (DiffieHellman.ddhDistAdvantage (1 : Scalar)
        (honestRejectDistinguisher (fun p => p.trusteeKeyProof.response.val) prepare (adversary b))) := by
  have h := honestReject_random_le (fun p => p.trusteeKeyProof.response.val) 1 generator_injective
    prepare (adversary b) 2 1 prepare_bound (cast_bound b)
  norm_num [noncePointBound] at h
  rw [loss_coercion] at h
  simpa only [div_eq_mul_inv] using h

/-- The finite real-world allowance is below one, not a vacuous bound. -/
theorem allowance_nonvacuous : (9/256 + 155/257 : ENNReal) < 1 := by
  have he : ENNReal.ofReal (9/256 + 155/257 : ℝ) = 9/256 + 155/257 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_div_of_pos (by norm_num),loss_coercion]
    norm_num
  rw [← he,ENNReal.ofReal_lt_one]
  norm_num

/-- An independent two-world table with rejection masses 0 and 1 refutes
omitting the advantage or substituting its half-sized guessing advantage. -/
theorem advantage_charge_required :
    ¬ (1 : ℝ) ≤ 0 ∧ (1 : ℝ) ≤ 0 + |0-1| ∧ ¬ (1 : ℝ) ≤ 0 + |0-1|/2 := by
  norm_num

/-- Changing the genuinely different guessing suffix cannot change this test;
the existing prefix controls separately check that those suffixes differ. -/
theorem guessing_does_not_change_rejection (b : Ballot Scalar Scalar 2) :
    honestRejectDistinguisher (fun p => p.trusteeKeyProof.response.val) prepare
      (fun initial => {adversary b initial with guessVote := fun _ _ => pure true}) =
    honestRejectDistinguisher (fun p => p.trusteeKeyProof.response.val) prepare (adversary b) := rfl

/-- The actual public rejection test has a derived interaction budget. -/
theorem cost_after_queries (b : Ballot Scalar Scalar 2) (g pk A T : Scalar) :
    (honestRejectDistinguisher (fun p => p.trusteeKeyProof.response.val) prepare (adversary b)
      g pk A T).IsTotalQueryBound 90 := by
  apply honestReject_total_bound _ _ _ _ _ _ _ 2 1 primeScalarSampler_total_bound
  · exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩
  · intro initial before
    exact ⟨by norm_num,fun _ => trivial⟩

#print axioms real_after_queries
#print axioms random_after_queries
#print axioms allowance_nonvacuous
#print axioms advantage_charge_required
#print axioms guessing_does_not_change_rejection
#print axioms cost_after_queries
end ExplainableCrypto.Helios.Computational.ElectionDDHRejectionControls
