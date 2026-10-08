import ExplainableCrypto.Helios.Symbolic.SourceRigidExecution
import ExplainableCrypto.Helios.Symbolic.SourceBoundRigiditySPOT
import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceRigidExecutionSPOT
open Historical General Source

abbrev body : Extended (Fin 1) :=
  .newVar (.par (.active none (.name 40)) (.plain (.output 0 (.name 41) (.input 8 .nil))))
abbrev captured : Extended (Option (Fin 1)) :=
  .newVar (.par (.active none (.name 40))
    (.par (.active (some none) (.name 41)) (.plain (.input 8 .nil))))
abbrev stopped : Extended (Option (Fin 1)) :=
  .newVar (.par (.active none (.name 40))
    (.par (.active (some none) (.name 41)) (.plain .nil)))
abbrev names : List SourceName := [.base 40,.channel 7]
abbrev before : Named (Fin 1) := Named.restrictNames names (.embed body)
abbrev afterOutput : Named (Option (Fin 1)) := Named.restrictNames names (.embed captured)
abbrev afterInput : Named (Option (Fin 1)) := Named.restrictNames names (.embed stopped)

/-- Arbitrary allocations, including assignments that collide, preserve the
independently fixed local value. No environment satisfies a changed value. -/
theorem scoped_source_has_all_opening_rigidity : before.LocallyRigid := by
  apply Named.LocallyRigid.restrictNames
  apply Named.LocallyRigid.embed
  intro ρ env
  refine ⟨?_,fun _ _ _ _ => ⟨True.intro,True.intro⟩⟩
  intro m n hm hn
  exact hm.1.trans hn.1.symm

theorem actual_named_scoped_output : Named.BoundOutput before 0 afterOutput := by
  apply Named.BoundOutput.restrictNames
  · exact .embed (.scope (.parRight _ (Extended.message_output 0 (.name 41) (.input 8 .nil))))
  · intro n hn
    simp only [names,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl <;> decide

theorem actual_output_target_has_all_opening_rigidity : afterOutput.LocallyRigid :=
  actual_named_scoped_output.locallyRigid scoped_source_has_all_opening_rigidity

theorem output_reclosure_is_exact : (Named.newVar afterOutput).LocallyRigid ↔ before.LocallyRigid :=
  actual_named_scoped_output.locallyRigid_reclose

/-- The next input uses the new public handle, retaining both the name prefix
and the distinct local binder. The process is not stuck after output. -/
theorem actual_input_uses_exported_handle :
    Named.FreeStep afterOutput (.input 8 (.var none)) afterInput := by
  apply Named.FreeStep.restrictNames
  · exact .embed (.scopeInput (.parRight _ (.parRight _ (.input 8 (.var (some none)) .nil))))
  · intro n hn
    simp only [names,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl <;> decide

theorem output_then_input_execution : Named.Execution before afterInput :=
  (Named.Execution.bound actual_named_scoped_output).trans (.free actual_input_uses_exported_handle)

theorem complete_execution_retains_rigidity : afterInput.LocallyRigid :=
  output_then_input_execution.locallyRigid scoped_source_has_all_opening_rigidity

/-- A chosen opening independently pins the private local to 50, while the
public capture remains the literal 41. Channel allocation is a separate sort. -/
theorem chosen_opening_retains_local_and_capture :
    Named.Opens afterInput NameAssignment.literal [.base 50,.channel 70]
      (.newVar (.par (.active none (.name 50))
        (.par (.active (some none) (.name 41)) (.plain .nil)))) := by
  apply Named.Opens.newName (.base 40) 50
  · apply Named.Opens.newName (.channel 7) 70
    · simpa [stopped,Extended.mapNames,Term.mapNames,Agent.mapNames,
        NameAssignment.base,NameAssignment.channel,NameAssignment.literal,SourceName.withValue] using
        Named.Opens.embed stopped (Function.update (Function.update NameAssignment.literal (.base 40) 50) (.channel 7) 70)
    · decide
  · decide

theorem correct_local_and_capture_values_satisfy :
    (Extended.newVar (.par (.active none (.name 50))
      (.par (.active (some none) (.name 41)) (.plain .nil))) : Extended (Option (Fin 1))).Satisfies
      (extendEnv (fun _ => .name 42) (.name 41)) :=
  ⟨.name 50,.refl _,.refl _,True.intro⟩

theorem changed_capture_value_is_rejected :
    ¬ (Extended.newVar (.par (.active none (.name 50))
      (.par (.active (some none) (.name 41)) (.plain .nil))) : Extended (Option (Fin 1))).Satisfies
      (extendEnv (fun _ => .name 42) (.name 50)) := by
  rintro ⟨m,_,he,_⟩
  have h := (EqE.name_iff 50 41).mp he
  cases h

theorem canonical_live_frame_excludes_cyclic_execution :
    ¬ Named.Execution
      (Named.restrictedState ∅ (⟨SourceLocalRigiditySPOT.publicFrame,SourceLocalRigiditySPOT.waiting⟩ : ScopedState ∅ 1))
      (.embed SourceLocalRigiditySPOT.padded) :=
  Named.canonical_no_execution_to_cycle _ _ _

theorem cyclic_joint_partner_is_not_a_reachable_partner :
    Named.JointOpening (.embed SourceLocalRigiditySPOT.padded)
      (.embed (Extended.frameProcess SourceLocalRigiditySPOT.publicFrame SourceLocalRigiditySPOT.waiting)) ∧
    ¬ Named.Execution
      (Named.restrictedState ∅ (⟨SourceLocalRigiditySPOT.publicFrame,SourceLocalRigiditySPOT.waiting⟩ : ScopedState ∅ 1))
      (.embed SourceLocalRigiditySPOT.padded) :=
  ⟨Extended.frame_with_unconstrained_local_joint _ _,canonical_live_frame_excludes_cyclic_execution⟩

theorem exporting_unconstrained_local_is_still_an_actual_action :
    Named.BoundOutput (.embed SourceBoundRigiditySPOT.exposedCycle) 0
      (.embed SourceBoundRigiditySPOT.exposedTarget) :=
  .embed SourceBoundRigiditySPOT.unconstrained_local_can_be_exported

theorem exported_unconstrained_target_is_locallyRigid :
    (Named.embed SourceBoundRigiditySPOT.exposedTarget).LocallyRigid := by
  apply Named.LocallyRigid.embed
  exact fun _ _ _ _ => ⟨True.intro,True.intro⟩

theorem exported_unconstrained_source_is_not_locallyRigid :
    ¬ (Named.embed SourceBoundRigiditySPOT.exposedCycle).LocallyRigid := by
  intro h
  have hr := h NameAssignment.literal [] _ (Named.Opens.embed _ _) Empty.elim
  simp only [show NameAssignment.literal.base = id from rfl,
    show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] at hr
  exact SourceBoundRigiditySPOT.target_rigidity_does_not_reflect_source.2.2 hr

theorem named_output_cannot_reflect_rigidity :
    ¬ (∀ (a : Named Empty) (b : Named (Option Empty)), Named.BoundOutput a 0 b →
      b.LocallyRigid → a.LocallyRigid) := by
  intro h
  exact exported_unconstrained_source_is_not_locallyRigid
    (h _ _ exporting_unconstrained_local_is_still_an_actual_action exported_unconstrained_target_is_locallyRigid)

theorem reclosed_unconstrained_target_is_not_locallyRigid :
    ¬ (Named.newVar (.embed SourceBoundRigiditySPOT.exposedTarget)).LocallyRigid :=
  fun h => exported_unconstrained_source_is_not_locallyRigid
    (exporting_unconstrained_local_is_still_an_actual_action.locallyRigid_reclose.mp h)

/-- A full canonical publication really crosses from Fin 1 through Option to
Fin 2, and structurally reconstructs the complete emitted frame. -/
theorem canonical_publication_execution_changes_domain :
    Named.Execution (Named.restrictedState Channels.canonical.privateChannels SourceScopedSPOT.emitting)
      (Named.restrictedState Channels.canonical.privateChannels SourceScopedSPOT.emitted) := by
  obtain ⟨m,ho,hs⟩ := SourceNameRestrictionSPOT.raw_output_and_capture_have_name_scope
  exact (Named.Execution.bound ho).trans
    ((Named.Execution.reindex _ Extended.outputHandle).trans (.structural hs))

theorem canonical_publication_execution_is_rigid :
    (Named.restrictedState Channels.canonical.privateChannels SourceScopedSPOT.emitted).LocallyRigid :=
  canonical_publication_execution_changes_domain.from_canonical SourceScopedSPOT.emitting

/-- A label-preserving private communication also progresses under a name
binder; plain continuation changes do not affect local solution uniqueness. -/
theorem private_communication_execution_is_rigid :
    Named.Execution
      (.newName (.channel 7) (.embed (.plain (.par (.output 7 (.name 40) .nil)
        (.input 7 (.output 0 (.var none) .nil))))) : Named Empty)
      (.newName (.channel 7) (.embed (.plain (.par .nil (.output 0 (.name 40) .nil)))) : Named Empty) ∧
    (Named.newName (.channel 7) (.embed (.plain (.par .nil (.output 0 (.name 40) .nil)))) : Named Empty).LocallyRigid := by
  have h := SourceNameRestrictionSPOT.private_communication_inside_binder
  refine ⟨.internal h,h.locallyRigid.mp ?_⟩
  apply Named.LocallyRigid.newName
  apply Named.LocallyRigid.embed
  exact fun _ _ => True.intro

end ExplainableCrypto.Helios.Symbolic.SourceRigidExecutionSPOT
