import ExplainableCrypto.Helios.Symbolic.SourceRecipeCaptureNormalization
import ExplainableCrypto.Helios.Symbolic.SourceNamedStaticEquivalence
import ExplainableCrypto.Helios.Symbolic.SourceExtendedSubstitutionSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceRecipeCaptureSPOT
open Historical General Source Extended

abbrev providers : Frame {40} 2 := ⟨fun i => if i = 0 then .name 40 else .name 41⟩
abbrev recipe : Recipe 2 := .spk (.var 0) (.var 1) (.const .one)
  (.binary .pair (.var 0) (.binary .pair (.var 1) (.name 42)))
abbrev payload : Ground := .spk (.name 40) (.name 41) (.const .one)
  (.binary .pair (.name 40) (.binary .pair (.name 41) (.name 42)))
abbrev wrongPayload : Ground := .spk (.name 40) (.name 41) (.const .one)
  (.binary .pair (.name 40) (.binary .pair (.name 41) (.name 43)))
abbrev continuation : Agent (Option (Fin 2)) := .input 8
  (.output 9 (.binary .pair (.var none) (.binary .pair (.var (some none)) (.var (some (some 0))))) .nil)
abbrev evaluated : Agent Empty := .input 8
  (.output 9 (.binary .pair (.var none) (.binary .pair (groundTerm payload) (.name 40))) .nil)
abbrev raw : Extended (Option (Fin 2)) :=
  .par ((activeFrame providers).rename some) (.par (.active none (shiftTerm recipe)) (.plain continuation))
noncomputable abbrev namedRaw : Named (Fin 3) :=
  (Named.restrictNames (Named.restrictionNames {7} {40}) (.embed raw)).rename outputHandle

theorem all_proof_fields_evaluate_exactly : providers.eval recipe = payload := rfl

theorem continuation_retains_input_and_exported_handles :
    continuation.subst (extendEnv providers.value payload) = evaluated := rfl

theorem exact_capture_reconstruction :
    Structural (raw.rename outputHandle) (frameProcess (providers.extend payload) evaluated) :=
  frame_recipe_capture_normalize providers recipe continuation

theorem old_and_new_frame_values_are_complete :
    (providers.extend payload).value 0 = .name 40 ∧
    (providers.extend payload).value 1 = .name 41 ∧
    (providers.extend payload).value 2 = payload := by decide

theorem fresh_naming_preserves_distinct_domains :
    outputHandle (none : Option (Fin 2)) = 2 ∧ outputHandle (some (0 : Fin 2)) = 0 ∧
    outputHandle (some (1 : Fin 2)) = 1 := by decide

theorem exact_named_capture_reconstruction :
    Named.Structural namedRaw (Named.restrictedState {7} ⟨providers.extend payload,evaluated⟩) :=
  Named.restricted_recipe_capture_normalize providers recipe continuation

theorem actual_new_frame_presentation : namedRaw.RepresentsFrame {7} (providers.extend payload) :=
  Named.restricted_recipe_capture_represents providers recipe continuation

theorem actual_new_frame_static_observation :
    Named.StaticEq namedRaw (Named.restrictedState {7} ⟨providers.extend payload,evaluated⟩) :=
  .of_presentations actual_new_frame_presentation (Named.restrictedState_represents _) (.refl _)

theorem changed_fourth_field_is_E_distinct : ¬ EqE payload wrongPayload := by
  intro h
  have h4 := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp h).2.2.2
  have ht := ((EqE.pair_iff _ _ _ _).mp h4).2
  have hn := ((EqE.pair_iff _ _ _ _).mp ht).2
  exact (by decide : (42 : Nat) ≠ 43) ((EqE.name_iff 42 43).mp hn)

theorem changed_capture_cannot_have_the_same_structural_target :
    ¬ Structural (raw.rename outputHandle) (frameProcess (providers.extend wrongPayload) evaluated) := by
  intro h
  have hv := (frameProcess_structural_values _ _ _ _ (exact_capture_reconstruction.symm.trans h)).1 (Fin.last 2)
  exact changed_fourth_field_is_E_distinct hv

/-- A real non-ground recipe output has both the original action derivation
and the full ground frame target, not only an existential emitted value. -/
theorem actual_recipe_output_and_reconstruction :
    BoundOutput (.par (activeFrame providers) (.plain (.output 0 recipe (.output 9 (.var 1) .nil)))) 0
      (.par ((activeFrame providers).rename some) (capture recipe (.output 9 (.var 1) .nil))) ∧
    Structural ((Extended.par ((activeFrame providers).rename some) (capture recipe (.output 9 (.var 1) .nil))).rename outputHandle)
      (frameProcess (providers.extend payload) (.output 9 (.name 41) .nil)) :=
  frame_recipe_output providers 0 recipe (.output 9 (.var 1) .nil)

abbrev localContext : Extended (Option (Fin 2)) := .newVar
  (.par (.active none (.binary .pair (.var (some (some 0))) (.var (some (some 1)))))
    (.plain (.input 8 (.output 9 (.binary .pair (.var none)
      (.binary .pair (.var (some none)) (.var (some (some none))))) .nil))))
abbrev scopedGrounded : Extended (Option (Fin 2)) := .newVar
  (.par (.active none (.binary .pair (.name 40) (.name 41)))
    (.plain (.input 8 (.output 9 (.binary .pair (.var none)
      (.binary .pair (.var (some none)) (.var (some (some none))))) .nil))))

theorem nested_local_and_input_instantiation_exact :
    Instantiates (liftSubst (fun i => groundTerm (providers.value i))) localContext scopedGrounded :=
  .newVar (.par (.active _ _ _ _ rfl) (.plain _ _))

theorem nested_context_normalization_retains_provider_frame :
    Structural (.par ((activeFrame providers).rename some) localContext)
      (.par ((activeFrame providers).rename some) scopedGrounded) :=
  shiftedFrame_apply_instantiates providers (by intro i; simp [Exports]) nested_local_and_input_instantiation_exact

theorem shifted_frame_does_not_ground_the_new_handle :
    entriesSubst 2 (some : Fin 2 → Option (Fin 2)) providers.value none = .var none :=
  entriesSubst_outside _ _ _ _ (by simp)

theorem shifted_frame_grounds_each_old_handle :
    entriesSubst 2 (some : Fin 2 → Option (Fin 2)) providers.value (some 0) = .name 40 ∧
    entriesSubst 2 (some : Fin 2 → Option (Fin 2)) providers.value (some 1) = .name 41 := by
  constructor <;> exact entriesSubst_value _ _ _ (Option.some_injective _) _

theorem provider_redefinition_violates_context_premise :
    ¬ (∀ i : Fin 2, ¬ (Extended.active (some (0 : Fin 2)) (.name 40)).Exports (some i)) :=
  fun h => h 0 rfl

theorem removed_provider_cannot_justify_grounding :
    ¬ Structural (.active (0 : Fin 2) (.var 1)) (.active 0 (.const .zero)) :=
  SourceExtendedSubstitutionSPOT.provider_constraint_cannot_be_omitted

theorem named_recipe_output_has_full_reconstructed_target :
    ∃ b : Named (Option (Fin 2)),
      Named.BoundOutput (Named.restrictNames (Named.restrictionNames {7} {40})
        (.embed (.par (activeFrame providers) (.plain (.output 0 recipe (.output 9 (.var 1) .nil)))))) 0 b ∧
      Named.Structural (b.rename outputHandle)
        (Named.restrictedState {7} ⟨providers.extend payload,.output 9 (.name 41) .nil⟩) :=
  Named.restricted_recipe_output providers 0 (by decide) recipe (.output 9 (.var 1) .nil)

end ExplainableCrypto.Helios.Symbolic.SourceRecipeCaptureSPOT
