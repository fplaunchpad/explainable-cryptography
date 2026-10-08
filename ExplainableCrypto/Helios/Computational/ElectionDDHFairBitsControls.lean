import ExplainableCrypto.Helios.Computational.ElectionSecrecyFairBits
import ExplainableCrypto.Helios.Computational.FairBitSamplerControls

/-! Actual sampling and paired-DDH controls. The toy additive group carries no
hardness assumption; it is used only to check events and statistical transport. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHFairBitsControls
open OracleComp OracleSpec ElectionDDHFairBits
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev F := ZMod 3

private def adaptive : DiffieHellman.DDHAdversary F F := fun _ _ _ T => do
  let x ← liftM (unifSpec.query 2)
  let y ← liftM (unifSpec.query (x.val+1))
  pure (decide (T = 0) != decide (y.val = x.val))

private theorem adaptive_bound (g A B T : F) : (adaptive g A B T).IsTotalQueryBound 2 := by
  exact ⟨by norm_num, fun _ => ⟨by norm_num, fun _ => trivial⟩⟩

/-- Both complete DDH experiments include the input-dependent, adaptive test. -/
theorem both_worlds :
    tvDist (DiffieHellman.ddhExpReal (1:F) (reduction 3 adaptive))
      (DiffieHellman.ddhExpReal (1:F) adaptive) ≤ 1/4 ∧
    tvDist (DiffieHellman.ddhExpRand (1:F) (reduction 3 adaptive))
      (DiffieHellman.ddhExpRand (1:F) adaptive) ≤ 1/4 := by
  constructor
  · convert real_distance 3 (1:F) adaptive 2 (adaptive_bound 1) using 1
    norm_num
  · convert random_distance 3 (1:F) adaptive 2 (adaptive_bound 1) using 1
    norm_num

/-- The actual two-game advantage receives both per-world allowances. -/
theorem adaptive_advantage :
    |DiffieHellman.ddhDistAdvantage (1:F) (reduction 3 adaptive)-
      DiffieHellman.ddhDistAdvantage (1:F) adaptive| ≤ 1/2 := by
  convert advantage_distance 3 (1:F) adaptive 2 (adaptive_bound 1) using 1
  norm_num

/-- The bridge retains the original fair-bit modulo bias in the ProbComp API. -/
theorem actual_modulo_bias :
    Pr[= (0:Fin 3) | bits 0 (liftM (unifSpec.query 2))] = (2:ENNReal)⁻¹ ∧
    Pr[= (0:Fin 3) | (liftM (unifSpec.query 2) : ProbComp (Fin 3))] = (3:ENNReal)⁻¹ := by
  constructor
  · norm_num [bits, runFairBitUniform, fairBitUniformImpl, sampleFairBitRange,
      sampleFairBitModulo_probability, show Nat.size 3 = 2 from rfl, id_map]
    change Pr[= (0:Fin 3) | sampleFairBitModulo 3 2] = (2:ENNReal)⁻¹
    norm_num [sampleFairBitModulo_probability]
    rw [show (4:ENNReal) = 2*2 from by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]
  · simp

/-- A deterministic observation still distinguishes different public inputs;
the transformation does not replace the given DDH challenge. -/
theorem public_input_retained :
    reduction (F := F) 7 (fun _ _ _ T : F => pure (decide (T=0))) 1 1 1 0 = pure true ∧
    reduction (F := F) 7 (fun _ _ _ T : F => pure (decide (T=0))) 1 1 1 1 = pure false := by
  norm_num [reduction, bits, runFairBitUniform]

/-- Two opposite changes in world probabilities require two allowances. -/
theorem one_world_allowance_fails :
    |(|(3/4:ℝ)-1/4| - |1/2-1/2|)| = 2*(1/4) ∧
    ¬ |(|(3/4:ℝ)-1/4| - |1/2-1/2|)| ≤ 1/4 := by norm_num

end ExplainableCrypto.Helios.Computational.ElectionDDHFairBitsControls
