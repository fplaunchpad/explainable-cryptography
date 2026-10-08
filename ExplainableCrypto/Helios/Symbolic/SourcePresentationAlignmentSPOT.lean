import ExplainableCrypto.Helios.Symbolic.SourcePresentationAlignment
import ExplainableCrypto.Helios.Symbolic.SourceFrameCompatibilitySPOT

namespace ExplainableCrypto.Helios.Symbolic.SourcePresentationAlignmentSPOT
open Historical General Source SourceFrameCompatibilitySPOT

abbrev capturedState : ScopedState {40} 1 := ⟨capturedPrivateFrame,.nil⟩

private theorem capture_structure :
    Named.Structural (Named.restrictedState ∅ capturedState) latentPrivateTarget := by
  simp only [Named.restrictedState,Named.restrictionNames,
    Finset.toList_singleton,Finset.toList_empty,List.map_cons,List.map_nil,List.append_nil,
    Named.restrictNames,List.foldr_cons,List.foldr_nil]
  exact .newName _ (.embed (Extended.Structural.zero _))

/-- A real output capture is first presented with extra unused private names;
its full joint witness then recovers the prescribed smaller policy. -/
theorem actual_capture_aligns_from_padded_policy :
    Named.BoundOutput latentPrivateOutput 0 latentPrivateCapture ∧
    latentPrivateTarget.RepresentsFrame {7,8}
      (capturedPrivateFrame.withPolicy ({40} ∪ {42,43})) ∧
    latentPrivateTarget.RepresentsFrame ∅ capturedState.frame := by
  have hp := latent_private_capture_has_full_private_presentation.pad_policy {7,8} {42,43}
    (by simp [Frame.nameSupport,Term.nameSupport])
  exact ⟨latent_private_name_has_actual_output,hp,
    (capture_structure.jointOpening capturedState).align_presentation hp⟩

/-- The captured name stays private; alignment cannot erase a used base name
from the target policy, even though it was absent from the old frame. -/
theorem actual_capture_cannot_align_to_empty_policy :
    ¬ ∃ (hidden : Finset Nat) (φ : Frame ∅ 1), latentPrivateTarget.RepresentsFrame hidden φ :=
  fun ⟨hidden,φ,h⟩ => latent_private_capture_has_no_empty_policy hidden φ h

/-- Full E, rather than syntactic identity, identifies retained provider values. -/
theorem ground_provider_reduction_has_actual_path :
    Extended.Structural (Extended.activeFrame SourcePolicyPaddingSPOT.leftExpanded)
      (Extended.activeFrame SourcePolicyPaddingSPOT.left) :=
  Extended.frameEntries_structural_of_values 1 id _ _ (fun _ => EqE.equation (.fst _ _))

/-- Different public bits cannot satisfy the semantic premise when both
frames already have actual presentations. -/
theorem unequal_providers_fail_same_realizations :
    ¬ (Extended.activeFrame SourcePolicyPaddingSPOT.zeros).SameRealizations
      (Extended.activeFrame SourcePolicyPaddingSPOT.ones) := by
  intro h
  have hs := (h.satisfies SourcePolicyPaddingSPOT.zeros.value).mp
    ((Extended.activeFrame_satisfies_iff _ _).mpr (fun _ => EqE.refl _))
  exact zero_not_one ((Extended.activeFrame_satisfies_iff _ _).mp hs 0)

/-- The inhabited cyclic pair still satisfies the semantic comparison but
fails the actual-presentation premise required by alignment. -/
theorem cyclic_joint_pair_still_fails_presentation :
    Named.JointOpening
      (.embed (.par (Extended.frameProcess capturedPrivateFrame .nil)
        (.newVar (.active none (.var none)))))
      (.embed (Extended.frameProcess capturedPrivateFrame .nil)) ∧
    ∀ (r hidden : Finset Nat) (φ : Frame r 1),
      ¬ (Named.embed (.par (Extended.frameProcess capturedPrivateFrame .nil)
        (.newVar (.active none (.var none))))).RepresentsFrame hidden φ :=
  ⟨Extended.frame_with_unconstrained_local_joint _ _,
    fun _ hidden φ => Named.frame_with_unconstrained_local_no_presentation _ _ φ hidden⟩

end ExplainableCrypto.Helios.Symbolic.SourcePresentationAlignmentSPOT
