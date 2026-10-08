import ExplainableCrypto.Helios.Symbolic.SourceCanonicalFrameProjection
import ExplainableCrypto.Helios.Symbolic.SourceBoundPrenexSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceFrameProjectionSPOT
open Historical General Source Extended

abbrev payload : Term (Fin 1) := .spk (.unary .pk (.name 40)) (.name 41) (.const .zero)
  (.ternary .penc (.unary .pk (.name 40)) (.name 48) (.const .one))
abbrev retained : Named (Fin 1) := .newName (.base 40) (.par (.embed (.active 0 payload))
  (.embed (.plain (.output 9 (.name 49) .nil))))

/-- Expected extraction is written literally, including the fourth proof
field and its nonce, the active domain and the private key restriction. -/
theorem complete_payload_and_restriction_retained : retained.frameOf =
    .newName (.base 40) (.par
      (.embed (.active 0 (.spk (.unary .pk (.name 40)) (.name 41) (.const .zero)
        (.ternary .penc (.unary .pk (.name 40)) (.name 48) (.const .one)))))
      (.embed (.plain .nil))) := rfl

theorem active_value_not_erased : retained.frameOf ≠
    .newName (.base 40) (.par (.embed (.plain .nil)) (.embed (.plain .nil))) := by
  intro h
  cases h

theorem changed_fourth_field_rejected : retained.frameOf ≠
    .newName (.base 40) (.par
      (.embed (.active 0 (.spk (.unary .pk (.name 40)) (.name 41) (.const .zero)
        (.ternary .penc (.unary .pk (.name 40)) (.name 48) (.const .zero)))))
      (.embed (.plain .nil))) := by
  intro h
  cases h

/-- The removed process's channel/name disappear, while the nonce used only
inside the retained proof ciphertext remains free. -/
theorem support_distinguishes_process_from_frame :
    SourceName.base 48 ∈ retained.frameOf.freeNames ∧
    SourceName.channel 9 ∉ retained.frameOf.freeNames ∧
    SourceName.base 49 ∉ retained.frameOf.freeNames ∧
    SourceName.base 40 ∉ retained.frameOf.freeNames := by decide

theorem alpha_transports_retained_frame :
    Named.Structural
      (Named.newName (.base 40) (.embed SourceNameInterpretationSPOT.binding)).frameOf
      (Named.newName (.base 50) (.embed (SourceNameInterpretationSPOT.binding.mapNames
        SourceNameInterpretationSPOT.e id))).frameOf :=
  SourceNameInterpretationSPOT.alpha_binding_representative.frameOf

theorem private_handshake_preserves_frame :
    Named.Structural SourceOperationalPrenexSPOT.beforeNamed.frameOf
      SourceOperationalPrenexSPOT.afterNamed.frameOf :=
  SourceOperationalPrenexSPOT.private_internal_reconstructed.frameOf

theorem alpha_input_preserves_frame :
    Named.Structural SourceOperationalPrenexSPOT.alphaSource.frameOf
      SourceOperationalPrenexSPOT.alphaTarget.frameOf :=
  SourceOperationalPrenexSPOT.alpha_input_reconstructed.frameOf

theorem nested_bound_output_recloses_frame :
    Named.Structural (.newVar SourceBoundPrenexSPOT.target.frameOf)
      SourceBoundPrenexSPOT.source.frameOf :=
  SourceBoundPrenexSPOT.scoped_bound_reconstructed.frameOf_reclose

theorem parallel_bound_output_recloses_old_context :
    Named.Structural
      (.newVar (Named.par SourceBoundPrenexSPOT.target
        (SourceBoundPrenexSPOT.oldContext.rename some)).frameOf)
      (Named.par SourceBoundPrenexSPOT.source SourceBoundPrenexSPOT.oldContext).frameOf :=
  (Named.BoundOutput.parLeft SourceBoundPrenexSPOT.oldContext
    SourceBoundPrenexSPOT.scoped_bound_reconstructed).frameOf_reclose

abbrev oldCapture : Extended (Option (Fin 1)) :=
  .par ((activeFrame SourceAtomicOutputSPOT.oldFrame).rename some)
    (capture (groundTerm SourceVisibleInterpretationSPOT.proofPayload) (groundAgent Agent.nil))

theorem actual_capture_keeps_old_and_fresh_exports :
    oldCapture.frameOf.Exports (some 0) ∧ oldCapture.frameOf.Exports none ∧
      (some (0 : Fin 1) : Option (Fin 1)) ≠ none := by
  simp [frameOf,activeFrame,frameEntries,rename,capture,Exports]

theorem actual_full_capture_recloses :
    Named.Structural (.newVar (.embed oldCapture.frameOf))
      (.embed (activeFrame SourceAtomicOutputSPOT.oldFrame)) :=
  (frame_output_derivable SourceAtomicOutputSPOT.oldFrame 0
    SourceVisibleInterpretationSPOT.proofPayload Agent.nil).frameOf_reclose.trans
      (.embed (frameProcess_frameOf _ _))

theorem unsatisfied_frame_constraint_rejected :
    ¬ (Extended.active (0 : Nat) (.const .one)).frameOf.Realizes
      (fun _ => .const .zero) .nil := fun h => zero_not_one h.1

theorem canonical_frame_constraints_satisfied :
    (frameProcess SourceAtomicOutputSPOT.oldFrame SourceInterpretationSPOT.privatePair).frameOf.Realizes
      SourceAtomicOutputSPOT.oldFrame.value .nil :=
  (frameProcess_realizes _ _).frameOf

/-- The existence result requires a satisfying environment, supplied here by
the actual complete frame; no claim fixes the returned body's behavior. -/
theorem canonical_frame_supplies_interpretation :
    ∃ p, (frameProcess SourceAtomicOutputSPOT.oldFrame SourceInterpretationSPOT.privatePair).Realizes
      SourceAtomicOutputSPOT.oldFrame.value p :=
  (frameOf_realizes_iff _ _).mp canonical_frame_constraints_satisfied

end ExplainableCrypto.Helios.Symbolic.SourceFrameProjectionSPOT
