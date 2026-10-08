import ExplainableCrypto.Helios.Computational.CoinDenominators

/-! Independent literal controls for the fair-bit representation boundary. -/
namespace ExplainableCrypto.Helios.Computational.CoinDenominatorsControls
open OracleComp OracleSpec

def pair : OracleComp coinSpec (Bool × Bool) := do
  let a ← coin
  let b ← coin
  pure (a,b)

def moduloThree : OracleComp coinSpec Nat := do
  let (a,b) ← pair
  pure (((if a then 2 else 0) + (if b then 1 else 0)) % 3)

/-- A single bit is exactly uniform. -/
theorem uniform_two (b : Bool) : Pr[= b | coin] = (2 : ENNReal)⁻¹ :=
  probOutput_coin b

/-- Two independent bits are exactly uniform on four outcomes. -/
theorem uniform_four (x : Bool × Bool) : Pr[= x | pair] = (4 : ENNReal)⁻¹ := by
  rcases x with ⟨a,b⟩
  simp [pair,probOutput_bind_eq_tsum,tsum_fintype]
  rw [← ENNReal.mul_inv] <;> norm_num

/-- Modulo reduction duplicates zero: its probability is 1/2, not 1/3. -/
theorem modulo_biased : Pr[= 0 | moduloThree] = (2 : ENNReal)⁻¹ ∧
    Pr[= 1 | moduloThree] = (4 : ENNReal)⁻¹ := by
  norm_num [moduloThree,pair,probOutput_bind_eq_tsum,probOutput_map_eq_sum_fintype_ite,tsum_fintype,Finset.filter_insert,Finset.filter_singleton]

  constructor
  · rw [← mul_add,ENNReal.inv_two_add_inv_two,mul_one]
  · rw [← ENNReal.mul_inv] <;> norm_num

/-- This excludes every terminating coin-only implementation, not just modulo. -/
theorem uniform_three_impossible (oa : OracleComp coinSpec (Fin 3)) :
    Pr[= 0 | oa] ≠ (3 : ENNReal)⁻¹ :=
  coinProgram_not_prime_uniform oa 3 (by decide) (by decide) 0

#print axioms uniform_two
#print axioms uniform_four
#print axioms modulo_biased
#print axioms uniform_three_impossible
end ExplainableCrypto.Helios.Computational.CoinDenominatorsControls
