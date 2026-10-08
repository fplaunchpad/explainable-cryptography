import ExplainableCrypto.Helios.Computational.BallotJointReplay
import ExplainableCrypto.Helios.Computational.BallotForkControls

/-! A repeated-target positive control checks that the shared-path algorithm
can succeed while retaining a challenge-dependent source value. It is not a
three-distinct-proof success bound. Disjoint first-path events refute multiplying
marginal successes without a common-path argument. -/
namespace ExplainableCrypto.Helios.Computational.BallotJointReplayControls
open OracleComp OracleSpec BallotForkControls StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable def taggedJoint := ballotJointReplay taggedProgram (fun _ => Prod.snd) 1

/-- Three conditional replays of this honest selected proof have a supported
joint success, derived from the checked positive single-fork control. -/
theorem tagged_joint_positive : 0 < Pr[fun out => out.isSome | taggedJoint] := by
  have hsingle : 0 < Pr[fun out => out.isSome |
      (do let path ← replayFirstPath (ballotReplaySourceRun taggedProgram)
          ballotReplaySourceAttempt taggedProgram Prod.snd 1 path)] := by
    rw [ballotReplaySourceAttempt_bind,tagged_project,probEvent_map]
    simpa only [Function.comp_def,Option.isSome_map] using honest_extraction_probability_positive
  obtain ⟨out,ho,hyes⟩ := probEvent_pos_iff.mp hsingle
  cases out with
  | none => simp at hyes
  | some w =>
    rw [mem_support_bind_iff] at ho
    obtain ⟨path,hpath,hw⟩ := ho
    apply probEvent_pos_iff.mpr
    refine ⟨some ((PFunctor.FreeM.output _ path).1,ballotJointWitnesses w w w),?_,rfl⟩
    rw [taggedJoint,ballotJointReplay,mem_support_bind_iff]
    refine ⟨path,hpath,?_⟩
    rw [support_map]
    refine ⟨some (ballotJointWitnesses w w w),?_,rfl⟩
    simp only [ballotJointReplayAtPath,mem_support_bind_iff,mem_support_pure_iff]
    exact ⟨some w,hw,some w,hw,some w,hw,rfl⟩

/-- The joint output tag follows its retained original full proof. A different
replay completion may have a different tag (the independent c=5/c=6 control). -/
theorem tagged_joint_original_tag (result : Bool × (BallotStatement Scalar × Proof01 Scalar Scalar))
    (w : Option (Fin 2) → BallotWitness Scalar)
    (ho : some (result,w) ∈ support taggedJoint) :
    result.1 = decide (result.2.2.zero.challenge = 3) := by
  obtain ⟨_,cache,hcache⟩ := ballotJointReplay_valid taggedProgram (fun _ => Prod.snd) 1 result w ho
  simp only [taggedProgram,runBallotOracle,simulateQ_map,StateT.run_map,support_map] at hcache
  obtain ⟨out,_,he⟩ := hcache
  have hr : (decide (out.1.2.zero.challenge = 3),out.1) = result := congrArg Prod.fst he
  rw [← hr]

/-- Each marginal can have a nonempty success set while joint success is
empty: separate existential first paths cannot establish one shared path. -/
theorem disjoint_marginals_no_shared_success :
    (∀ i : Fin 2, ∃ tag : Bool, tag = decide (i = 0)) ∧
      ¬ (∃ tag : Bool, ∀ i : Fin 2, tag = decide (i = 0)) := by decide

#print axioms tagged_joint_positive
#print axioms tagged_joint_original_tag
#print axioms disjoint_marginals_no_shared_success
end ExplainableCrypto.Helios.Computational.BallotJointReplayControls
