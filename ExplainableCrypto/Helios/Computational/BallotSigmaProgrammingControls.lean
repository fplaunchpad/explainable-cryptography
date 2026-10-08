import ExplainableCrypto.Helios.Computational.BallotSigmaProgramming
import Mathlib.Algebra.Field.ZMod

/-! Controls for the two distinct premises of simulator programming properties. -/
namespace ExplainableCrypto.Helios.Computational.BallotSigmaProgrammingControls

open OracleComp
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- Without generator injectivity, all four commitment coordinates can be constant. -/
theorem zero_generator_constant_commitment :
    Pr[fun t => t.1 = ((0,0),(0,0)) |
      ballotFullSimTranscript (F := F) (⟨0,0,(0,0)⟩ : BallotStatement F)] = 1 := by
  simp [ballotFullSimTranscript, ballotSimCommit, simulatedBranch]
  grind

/-- The resulting probability violates the proposed unconditional point bound. -/
theorem zero_generator_refutes_unconditional_bound :
    ¬ Pr[fun t => t.1 = ((0,0),(0,0)) |
      ballotFullSimTranscript (F := F) (⟨0,0,(0,0)⟩ : BallotStatement F)] ≤
        (Fintype.card F : ENNReal)⁻¹ := by
  rw [zero_generator_constant_commitment]
  have hq : (1 : ENNReal) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card (α := F)
  exact not_le.mpr (ENNReal.inv_lt_one.mpr hq)

/-- Unit generator gives a nonvacuous point-bound instance, with a valid ballot. -/
theorem unit_generator_point_bound (pc : BallotCommitment F) :
    Pr[fun t => t.1 = pc |
      ballotFullSimTranscript (F := F) (⟨1,2,encryptWith (F := F) 1 2 1 0⟩ : BallotStatement F)] ≤
        (Fintype.card F : ENNReal)⁻¹ := by
  apply ballotSim_commit_probability_le
  intro x y h
  simpa using h

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev Scalar := ZMod 3
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def nonbitStatement : BallotStatement Scalar := ⟨1,2,(1,1)⟩

theorem nonbit_has_no_witness : ¬ ∃ wit : BallotWitness Scalar,
    nonbitStatement.Witnesses wit := by decide

theorem nonbit_zero_commit_forces_challenge : ∀ (c : Scalar) (resp : BallotResponse Scalar),
    ballotSimCommit nonbitStatement c resp = ((0,0),(0,0)) → c = 0 := by decide

/-- Removing the valid-witness premise makes conditional challenge uniformity
false, even with an injective generator and a nonzero public key. -/
theorem nonbit_refutes_unconditional_challenge_uniformity :
    Pr[fun t => t.1 = ((0,0),(0,0)) ∧ t.2.1 = 1 |
      ballotFullSimTranscript (F := Scalar) nonbitStatement] ≠
    Pr[fun t => t.1 = ((0,0),(0,0)) | ballotFullSimTranscript (F := Scalar) nonbitStatement] *
      (Fintype.card Scalar : ENNReal)⁻¹ := by
  have hz : Pr[fun t => t.1 = ((0,0),(0,0)) ∧ t.2.1 = 1 |
      ballotFullSimTranscript (F := Scalar) nonbitStatement] = 0 := by
    apply probEvent_eq_zero_iff.mpr
    intro t ht hbad
    simp only [ballotFullSimTranscript, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at ht
    obtain ⟨c, _, e, _, z₀, _, z₁, _, rfl⟩ := ht
    have hc := nonbit_zero_commit_forces_challenge c (e,z₀,z₁) hbad.1
    exact zero_ne_one (hc.symm.trans hbad.2)
  have hp : Pr[fun t => t.1 = ((0,0),(0,0)) |
      ballotFullSimTranscript (F := Scalar) nonbitStatement] ≠ 0 := by
    apply probEvent_ne_zero_iff.mpr
    refine ⟨(ballotSimCommit (F := Scalar) nonbitStatement 0 (0,0,0), 0, (0,0,0)), ?_, by decide⟩
    simp only [ballotFullSimTranscript, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨0, by simp, 0, by simp, 0, by simp, 0, by simp, rfl⟩
  rw [hz]
  exact Ne.symm (mul_ne_zero hp (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)))

#print axioms nonbit_has_no_witness
#print axioms nonbit_zero_commit_forces_challenge
#print axioms nonbit_refutes_unconditional_challenge_uniformity

#print axioms zero_generator_constant_commitment
#print axioms zero_generator_refutes_unconditional_bound
#print axioms unit_generator_point_bound

end ExplainableCrypto.Helios.Computational.BallotSigmaProgrammingControls
