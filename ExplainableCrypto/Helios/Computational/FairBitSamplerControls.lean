import ExplainableCrypto.Helios.Computational.FairBitSampler
import ExplainableCrypto.Helios.Computational.CoinDenominators

/-! Literal controls retain digit order, exact power-of-two laws and residual bias. -/
namespace ExplainableCrypto.Helios.Computational.FairBitSamplerControls
open OracleComp OracleSpec

/-- Mathlib's executed digit encoding uses the first bit as the low bit. -/
theorem literal_digit_order :
    finFunctionFinEquiv (![1,0] : Fin 2 → Fin 2) = 1 ∧
    finFunctionFinEquiv (![0,1] : Fin 2 → Fin 2) = 2 := by decide

/-- Modulo reduction is exact when four equally likely indices cover four residues. -/
theorem power_of_two_exact :
    evalSPMF (sampleFairBitModulo 4 2) = evalSPMF (uniformSample (Fin 4)) := by
  apply evalSPMF_ext
  intro y
  simp [sampleFairBitModulo_probability]

/-- Three extra bits give masses 11/32 and 10/32; the bias is accounted for,
not erased. This is the actual selected sampler at range three. -/
theorem extra_bits_still_biased :
    Pr[= (0 : Fin 3) | sampleFairBitRange 3 3] = 11 * (32 : ENNReal)⁻¹ ∧
    Pr[= (2 : Fin 3) | sampleFairBitRange 3 3] = 10 * (32 : ENNReal)⁻¹ ∧
    Pr[= (0 : Fin 3) | sampleFairBitRange 3 3] ≠ (3 : ENNReal)⁻¹ := by
  refine ⟨?_,?_,coinProgram_not_prime_uniform _ 3 (by decide) (by decide) 0⟩
  · norm_num [sampleFairBitRange,sampleFairBitModulo_probability,show Nat.size 3 = 2 from rfl]
  · norm_num [sampleFairBitRange,sampleFairBitModulo_probability,show Nat.size 3 = 2 from rfl]

/-- The selected q=3/slack=3 sampler consumes at most five fair-bit requests
and meets its 1/8 statistical budget. Local-operation costs are not asserted. -/
theorem literal_budget :
    (sampleFairBitRange 3 3).IsTotalQueryBound 5 ∧
    SPMF.tvDist (evalSPMF (sampleFairBitRange 3 3))
      (evalSPMF (uniformSample (Fin 3))) ≤ (8 : ℝ)⁻¹ := by
  constructor
  · exact sampleFairBitRange_query_bound 3 3
  · simpa only [show (2 : ℝ)^3 = 8 by norm_num] using sampleFairBitRange_tv_le 3 3

#print axioms literal_digit_order
#print axioms power_of_two_exact
#print axioms extra_bits_still_biased
#print axioms literal_budget
end ExplainableCrypto.Helios.Computational.FairBitSamplerControls
