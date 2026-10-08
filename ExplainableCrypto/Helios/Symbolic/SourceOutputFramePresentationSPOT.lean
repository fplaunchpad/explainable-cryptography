import ExplainableCrypto.Helios.Symbolic.SourceReachableFramePresentation
import ExplainableCrypto.Helios.Symbolic.SourceCapturedEquationsSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceOutputFramePresentationSPOT
open Historical General Source Extended

/-- Copying a cyclic public equation preserves the equation; it does not
silently eliminate its unconstrained value. -/
theorem cyclic_copy_preserves_its_equation :
    BinderStructural (captureCopy (.active none (.var none) : Extended (Option (Fin 0))))
      (.active none (.var none)) := captureCopy_structural _ True.intro rfl

/-- The universal copy proof covers a selected provider under two dependent
locals and retains the unrelated old public provider. -/
theorem dependent_local_copy_preserves_the_full_frame :
    BinderStructural (captureCopy SourceVariableFramePrefixSPOT.raw) SourceVariableFramePrefixSPOT.raw := by
  apply captureCopy_structural
  · simp [UniqueDefinitions,Exports]
  · simp [Exports]

/-- Even an empty old private policy suffices: the general theorem recovers
an actual target policy from the full live process's fresh name opening. -/
theorem private_output_reconstructs_its_policy :
    ∃ (policy channels : Finset Nat) (φ : Frame policy 1),
      SourceFrameCompatibilitySPOT.latentPrivateTarget.RepresentsFrame channels φ :=
  SourceFrameCompatibilitySPOT.latent_private_name_has_actual_output.exists_frame_presentation
    SourceFrameCompatibilitySPOT.latent_private_name_is_absent_from_old_frame_policy

theorem reconstructed_policy_cannot_be_the_old_empty_policy :
    ¬ ∃ (channels : Finset Nat) (φ : Frame ∅ 1),
      SourceFrameCompatibilitySPOT.latentPrivateTarget.RepresentsFrame channels φ := by
  rintro ⟨channels,φ,h⟩
  exact SourceFrameCompatibilitySPOT.latent_private_capture_has_no_empty_policy channels φ h

/-- A real historical run with two outputs, adaptive replay input and rejection
now has a complete structural presentation, for either voter assignment. -/
theorem actual_rejected_execution_has_full_presentation (swap : Bool) :
    ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : Fin 3 ≃ Fin phase.handles),
      Process.Reachable SourceReachableElectionSPOT.ns swap SourceReachableElectionSPOT.left
        SourceReachableElectionSPOT.right 1 phase ∧
      ((SourceReachableElectionSPOT.raw swap (.rejected [])).rename i).RepresentsFrame
        (Channels.canonical.privateChannels.image k)
        ((sourceView SourceReachableElectionSPOT.ns swap SourceReachableElectionSPOT.left
          SourceReachableElectionSPOT.right phase).mapNames e) := by
  have hl : NoncesFreshFor SourceReachableElectionSPOT.ns SourceReachableElectionSPOT.left.value := by
    unfold NoncesFreshFor
    decide
  have hr : NoncesFreshFor SourceReachableElectionSPOT.ns SourceReachableElectionSPOT.right.value := by
    unfold NoncesFreshFor
    decide
  obtain ⟨phase,e,k,i,hphase,_,hp⟩ := source_reachable_frame_presentation _
    NumericReflectionSPOT.fixture_names_fresh swap _ _ hl hr 1 _ Channels.canonical_fresh
    (SourceReachableElectionSPOT.actual_mixed_execution_rejects swap)
  exact ⟨phase,e,k,i,hphase,hp⟩

end ExplainableCrypto.Helios.Symbolic.SourceOutputFramePresentationSPOT
