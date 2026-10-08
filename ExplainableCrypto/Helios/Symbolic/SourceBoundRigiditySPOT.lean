import ExplainableCrypto.Helios.Symbolic.SourcePresentationRigidity
import ExplainableCrypto.Helios.Symbolic.SourceLocalRigiditySPOT
import ExplainableCrypto.Helios.Symbolic.SourceVisibleInterpretationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceBoundRigiditySPOT
open Historical General Source Extended

abbrev dependentBody : Extended (Option (Option Empty)) :=
  .par (.active (some none) (.name 40)) (.active none (.binary .pair (.var (some none)) (.name 41)))
abbrev dependentLocals : Extended Empty := .newVar (.newVar dependentBody)

/-- The inner local depends on the outer one, so binder commutation must
preserve their coordinates as well as uniqueness modulo E. -/
theorem dependent_locals_are_rigid : dependentLocals.Rigid Empty.elim := by
  refine ⟨?_,?_⟩
  · rintro v w ⟨m,hm⟩ ⟨n,hn⟩
    exact hm.1.trans hn.1.symm
  · rintro v ⟨m,hm⟩
    refine ⟨?_,fun _ _ _ _ => ⟨True.intro,True.intro⟩⟩
    intro n k hn hk
    exact hn.2.trans hk.2.symm

theorem exchanged_dependent_locals_are_rigid :
    (Extended.newVar (.newVar (dependentBody.rename swapBinders))).Rigid Empty.elim :=
  (rigid_varComm dependentBody Empty.elim).mp dependent_locals_are_rigid

theorem exchanged_dependent_values_satisfy :
    (dependentBody.rename swapBinders).Satisfies
      (extendEnv (extendEnv Empty.elim (.binary .pair (.name 40) (.name 41))) (.name 40)) := by
  rw [satisfies_rename,extendEnv_swapBinders]
  exact ⟨.refl _,.refl _⟩

theorem exchange_has_actual_named_path :
    Named.Structural (.embed dependentLocals)
      (.embed (.newVar (.newVar (dependentBody.rename swapBinders)))) :=
  (BinderStructural.varComm dependentBody).named

abbrev scopedSource := SourceVisibleInterpretationSPOT.scopedSource
abbrev scopedTarget := SourceVisibleInterpretationSPOT.scopedTarget

theorem scoped_source_is_rigid (env : Fin 1 → Ground) : scopedSource.Rigid env := by
  refine ⟨?_,fun _ _ _ _ => ⟨True.intro,True.intro⟩⟩
  intro m n hm hn
  exact hm.1.trans hn.1.symm

theorem actual_scope_output_recloses_rigidity (env : Fin 1 → Ground) :
    (Extended.newVar scopedTarget).Rigid env ↔ scopedSource.Rigid env :=
  SourceAtomicOutputSPOT.output_crosses_variable_scope.rigid_reclose env

theorem actual_scope_output_preserves_all_target_locals (env : Option (Fin 1) → Ground) :
    scopedTarget.Rigid env :=
  SourceAtomicOutputSPOT.output_crosses_variable_scope.rigid_all_targets scoped_source_is_rigid env

theorem scope_values_remain_distinct :
    ¬ EqE (extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 41)) (.name 40) none)
      (extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 40)) (.name 41) none) :=
  SourceVisibleInterpretationSPOT.omitted_scope_exchange_rejected

abbrev exposedCycleBody : Extended (Option Empty) :=
  .par (.active none (.var none)) (.plain (.output 0 (.var none) .nil))
abbrev exposedCycle : Extended Empty := .newVar exposedCycleBody
abbrev exposedTarget : Extended (Option Empty) := .par (.active none (.var none)) (.plain .nil)

theorem unconstrained_local_can_be_exported : BoundOutput exposedCycle 0 exposedTarget :=
  .openAtom (.parRight _ (.output 0 none .nil))

private theorem exposed_source_not_rigid : ¬ exposedCycle.Rigid Empty.elim := by
  intro h
  have he := h.1 (.name 40) (.name 41) ⟨.refl _,True.intro⟩ ⟨.refl _,True.intro⟩
  have hn := (EqE.name_iff 40 41).mp he
  cases hn

/-- Removing the exported binder can hide a former uniqueness failure.
Target rigidity alone therefore cannot justify source rigidity. -/
theorem target_rigidity_does_not_reflect_source :
    BoundOutput exposedCycle 0 exposedTarget ∧ (∀ env, exposedTarget.Rigid env) ∧
      ¬ exposedCycle.Rigid Empty.elim :=
  ⟨unconstrained_local_can_be_exported,fun _ _ _ => ⟨True.intro,True.intro⟩,exposed_source_not_rigid⟩

theorem reclosure_retains_the_uniqueness_failure : ¬ (Extended.newVar exposedTarget).Rigid Empty.elim := by
  intro h
  exact exposed_source_not_rigid ((unconstrained_local_can_be_exported.rigid_reclose Empty.elim).mp h)

/-- Full Named rules cannot repair the earlier embedded cyclic counterexample. -/
theorem full_named_cycle_cannot_normalize :
    ¬ Named.Structural (.embed SourceLocalRigiditySPOT.cycle) (.embed SourceLocalRigiditySPOT.emptyState) :=
  Named.unconstrained_local_not_structural

theorem full_named_live_frame_cannot_normalize :
    ¬ Named.Structural (.embed SourceLocalRigiditySPOT.padded)
      (.embed (frameProcess SourceLocalRigiditySPOT.publicFrame SourceLocalRigiditySPOT.waiting)) :=
  Named.frame_with_unconstrained_local_not_structural _ _

/-- JointOpening itself remains inhabited for the separated complete pair. -/
theorem joint_opening_is_not_named_structural :
    Named.JointOpening (.embed SourceLocalRigiditySPOT.padded)
      (.embed (frameProcess SourceLocalRigiditySPOT.publicFrame SourceLocalRigiditySPOT.waiting)) ∧
    ¬ Named.Structural (.embed SourceLocalRigiditySPOT.padded)
      (.embed (frameProcess SourceLocalRigiditySPOT.publicFrame SourceLocalRigiditySPOT.waiting)) :=
  ⟨frame_with_unconstrained_local_joint _ _,full_named_live_frame_cannot_normalize⟩

theorem changing_frame_values_or_policy_cannot_present_cycle {restricted : Finset Nat}
    (φ : Frame restricted 1) (hidden : Finset Nat) :
    ¬ (Named.embed SourceLocalRigiditySPOT.padded).RepresentsFrame hidden φ :=
  Named.frame_with_unconstrained_local_no_presentation _ _ φ hidden

theorem joint_opening_does_not_supply_static_observation :
    Named.JointOpening (.embed SourceLocalRigiditySPOT.padded)
      (.embed (frameProcess SourceLocalRigiditySPOT.publicFrame SourceLocalRigiditySPOT.waiting)) ∧
    ¬ Named.StaticEq (.embed SourceLocalRigiditySPOT.padded)
      (.embed (frameProcess SourceLocalRigiditySPOT.publicFrame SourceLocalRigiditySPOT.waiting)) :=
  ⟨frame_with_unconstrained_local_joint _ _,Named.frame_with_unconstrained_local_no_staticEq _ _ _⟩

/-- The actual canonical state still has a complete static observation witness. -/
theorem canonical_static_observation_remains_available :
    Named.StaticEq (Named.restrictedState ∅
      (⟨SourceLocalRigiditySPOT.publicFrame,SourceLocalRigiditySPOT.waiting⟩ : ScopedState ∅ 1))
      (Named.restrictedState ∅ (⟨SourceLocalRigiditySPOT.publicFrame,SourceLocalRigiditySPOT.waiting⟩ : ScopedState ∅ 1)) :=
  (Named.restrictedState_represents _).staticEq_self

end ExplainableCrypto.Helios.Symbolic.SourceBoundRigiditySPOT
