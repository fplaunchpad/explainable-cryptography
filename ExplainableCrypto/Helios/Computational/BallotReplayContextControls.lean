import ExplainableCrypto.Helios.Computational.BallotJointReplayBound
import ExplainableCrypto.Helios.Computational.BallotJointReplayControls

/-! Threshold reachability is necessary. The new quantitative bound is also
strictly positive on the existing honest tagged raw source, not merely a
nonnegative inequality satisfied by an always-failing extractor. -/
namespace ExplainableCrypto.Helios.Computational.BallotReplayContextControls
open OracleComp OracleSpec BallotForkControls StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Without occurrence reachability, even a pure selected output has zero
context mass and positive bad-event probability at threshold zero. -/
theorem missing_occurrence_refutes_bound :
    Pr[fun path => True ∧ ballotReplayContextMass
        (pure () : OracleComp (FiatShamir.Fork.wrappedSpec Scalar) Unit)
        (.inr ()) 0 (fun _ => True) path ≤ 0 |
      replayFirstPath (pure () : OracleComp (FiatShamir.Fork.wrappedSpec Scalar) Unit)] = 1 := by
  simp [replayFirstPath,ballotReplayContextMass]

private theorem tagged_selection_one :
    Pr[fun path => ∀ _ : Option (Fin 2),
      (ballotForkSelector 1 (PFunctor.FreeM.output _
        (ballotReplaySourcePath taggedProgram Prod.snd path))).isSome |
      replayFirstPath (ballotReplaySourceRun taggedProgram)] = 1 := by
  have hp : Pr[fun path => (ballotForkSelector 1 (PFunctor.FreeM.output _ path)).isSome |
      replayFirstPath (ballotForkRunTrace (Prod.snd <$> taggedProgram))] = 1 := by
    have h := congrArg (fun m => Pr[fun trace => (ballotForkSelector 1 trace).isSome | m])
      (map_output_replayFirstPath (ballotForkRunTrace (Prod.snd <$> taggedProgram)))
    simp only [probEvent_map,Function.comp_def] at h
    rw [h,tagged_project]
    exact honest_selector_probability_one
  rw [← ballotReplaySourcePath_distribution taggedProgram Prod.snd,probEvent_map] at hp
  simpa only [forall_const,Function.comp_def] using hp

/-- With δ=1/8 and q=11, the proved common-path bound is 27/2725888,
strictly positive. The control repeats one honest target three times. -/
theorem tagged_joint_quantitative :
    (27 / 2725888 : ENNReal) ≤ Pr[fun out => out.isSome | BallotJointReplayControls.taggedJoint] := by
  have h := ballotJointReplay_selection_le taggedProgram (fun _ => Prod.snd) 1 (1/8)
  dsimp only at h
  rw [tagged_selection_one] at h
  norm_num [Scalar, ZMod.card] at h
  have hc : (1 - 6*(8 : ENNReal)⁻¹) * ((8 : ENNReal)⁻¹ - 11⁻¹)^3 = 27 / 2725888 := by
    have hn : (1 - 6*(8 : NNReal)⁻¹) * ((8 : NNReal)⁻¹ - 11⁻¹)^3 = 27 / 2725888 := by
      apply NNReal.eq
      norm_num [NNReal.coe_sub_def]
    simpa [ENNReal.coe_sub, ENNReal.coe_inv, ENNReal.coe_div] using
      congrArg (fun x : NNReal => (x : ENNReal)) hn
  rw [hc] at h
  exact h

theorem tagged_joint_bound_positive : (0 : ENNReal) < 27 / 2725888 := by norm_num

#print axioms missing_occurrence_refutes_bound
#print axioms tagged_joint_quantitative
#print axioms tagged_joint_bound_positive
end ExplainableCrypto.Helios.Computational.BallotReplayContextControls
