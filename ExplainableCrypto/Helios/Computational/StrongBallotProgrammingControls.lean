import ExplainableCrypto.Helios.Computational.StrongBallotProgrammingDistance
import ExplainableCrypto.Helios.Computational.StrongBallotOracleControls

/-! State-inclusive controls: an empty-cache bound for the literal q=11
statement, and a populated cache that exposes the internal collision flag.
The flag is reduction state, not a public election observation. -/
namespace ExplainableCrypto.Helios.Computational.StrongBallotProgrammingControls

open OracleComp OracleSpec StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

theorem empty_cache_distance_le :
    tvDist ((strongBallotRealOracle stmt (false,3)).run ∅)
      ((strongBallotSimOracle (F := Scalar) stmt).run ∅) ≤ 3 / 11 := by
  have hw : stmt.Witnesses (false,(3 : Scalar)) := by decide
  have hg : Function.Injective (fun r : Scalar => r • stmt.generator) := by
    intro a b h
    simpa [stmt, smul_eq_mul] using h
  have h := strongBallot_programming_step_distance_le stmt (false,3) hw hg ∅ ∅
    (by simp)
  simpa [div_eq_mul_inv] using h

def populated : BallotOracleCache Scalar Scalar := fun _ => some 1

theorem populated_simulator_flags :
    Pr[fun out => out.1.2 = true |
      (strongBallotSimOracle (F := Scalar) stmt).run populated] = 1 := by
  rw [strongBallotSimOracle_bad_probability]
  simp [populated]

theorem populated_actual_does_not_flag :
    Pr[fun out => out.1.2 = true |
      (strongBallotRealOracle stmt (false,(3 : Scalar))).run populated] = 0 := by
  simp [strongBallotRealOracle, StateT.run]

/-- Discarding the collision event would identify distributions separated by
the retained internal flag. Scalar and group are finite in this control. -/
theorem populated_distributions_differ :
    𝒮[(strongBallotRealOracle stmt (false,(3 : Scalar))).run populated] ≠
      𝒮[(strongBallotSimOracle (F := Scalar) stmt).run populated] := by
  intro h
  have he := probEvent_congr' (p := fun out => out.1.2 = true)
    (fun _ _ => Iff.rfl) h
  rw [populated_actual_does_not_flag, populated_simulator_flags] at he
  exact zero_ne_one he

#print axioms empty_cache_distance_le
#print axioms populated_simulator_flags
#print axioms populated_actual_does_not_flag
#print axioms populated_distributions_differ

end ExplainableCrypto.Helios.Computational.StrongBallotProgrammingControls
