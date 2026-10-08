import ExplainableCrypto.Helios.Symbolic.SourceTermProgramCapture
import ExplainableCrypto.Helios.Symbolic.SourceRecipeCaptureSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceProgramCaptureSPOT
open Historical General Source Extended

abbrev providers : Frame {40} 2 := SourceRecipeCaptureSPOT.providers
abbrev program : TermProgram (Fin 2) := .letTerm (.var 0)
  (.letTerm (.binary .pair (.var none) (.var (some 1)))
    (.result (.spk (.var (some none)) (.var none) (.const .one)
      (.binary .pair (.var (some (some 0))) (.var none)))))
abbrev computedRecipe : Recipe 2 := .spk (.var 0) (.binary .pair (.var 0) (.var 1)) (.const .one)
  (.binary .pair (.var 0) (.binary .pair (.var 0) (.var 1)))
abbrev payload : Ground := .spk (.name 40) (.binary .pair (.name 40) (.name 41)) (.const .one)
  (.binary .pair (.name 40) (.binary .pair (.name 40) (.name 41)))
abbrev wrongPayload : Ground := .spk (.name 41) (.binary .pair (.name 40) (.name 41)) (.const .one)
  (.binary .pair (.name 40) (.binary .pair (.name 40) (.name 41)))

/-- Independently written Scope target: x=old0 stays the outer local;
y=pair(x,old1) stays the inner local; the capture is outside both. -/
abbrev rawTarget : Extended (Option (Fin 2)) := .newVar
  (.par (.active none (.var (some (some 0))))
    (.newVar (.par (.active none (.binary .pair (.var (some none)) (.var (some (some (some 1))))))
      (.par (.active (some (some none))
        (.spk (.var (some none)) (.var none) (.const .one)
          (.binary .pair (.var (some (some (some 0)))) (.var none)))) (.plain .nil)))))

theorem dependent_computation_is_nontrivial : program.bindings = 2 ∧ program.value = computedRecipe := ⟨rfl,rfl⟩

theorem dependent_computation_has_full_expected_value : providers.eval program.value = payload := rfl

theorem raw_scope_target_retains_both_locals : program.capture = rawTarget := rfl

theorem actual_output_crosses_both_local_scopes : BoundOutput (program.compile 0) 0 rawTarget :=
  program.compile_output_capture 0

theorem both_locals_eliminate_after_the_actual_output :
    Structural rawTarget (Extended.capture computedRecipe .nil) := program.capture_normalizes

theorem captured_handle_is_outside_both_locals : rawTarget.Exports none :=
  (program.capture_exports_iff none).mpr rfl

theorem no_old_handle_is_exported_by_the_computation (i : Fin 2) : ¬ rawTarget.Exports (some i) :=
  fun h => Option.some_ne_none i ((program.capture_exports_iff (some i)).mp h)

theorem full_frame_reconstructs_dependent_capture :
    Structural ((Extended.par ((activeFrame providers).rename some) rawTarget).rename outputHandle)
      (frameProcess (providers.extend payload) .nil) := frame_program_capture_normalize providers program

theorem real_output_retains_complete_old_frame :
    BoundOutput (.par (activeFrame providers) (program.compile 0)) 0
      (.par ((activeFrame providers).rename some) rawTarget) :=
  (frame_program_output providers program 0).1

theorem reconstructed_values_keep_both_providers_and_full_result :
    (providers.extend payload).value 0 = .name 40 ∧ (providers.extend payload).value 1 = .name 41 ∧
    (providers.extend payload).value 2 = payload := by decide

theorem wrong_full_result_is_E_distinct : ¬ EqE payload wrongPayload := by
  intro h
  have hn := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp h).1
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp hn)

theorem wrong_result_cannot_normalize_from_raw_target :
    ¬ Structural ((Extended.par ((activeFrame providers).rename some) rawTarget).rename outputHandle)
      (frameProcess (providers.extend wrongPayload) .nil) := by
  intro h
  have hv := (frameProcess_structural_values _ _ _ _ (full_frame_reconstructs_dependent_capture.symm.trans h)).1 (Fin.last 2)
  exact wrong_full_result_is_E_distinct hv

theorem merging_fresh_capture_into_old_handle_is_not_structural :
    ¬ Structural rawTarget (rawTarget.rename (fun _ => some (0 : Fin 2))) := by
  intro h
  have he := (h.exports none).mp captured_handle_is_outside_both_locals
  simp [rename,Exports] at he

noncomputable abbrev namedTarget : Named (Fin 3) :=
  (Named.restrictNames (Named.restrictionNames {7} {40})
    (.embed (.par ((activeFrame providers).rename some) rawTarget))).rename outputHandle

theorem dependent_capture_has_actual_named_presentation :
    namedTarget.RepresentsFrame {7} (providers.extend payload) :=
  Named.restricted_program_capture_represents providers program

theorem dependent_capture_has_actual_static_observation :
    Named.StaticEq namedTarget (Named.restrictedState {7} ⟨providers.extend payload,.nil⟩) :=
  .of_presentations dependent_capture_has_actual_named_presentation (Named.restrictedState_represents _) (.refl _)

theorem original_named_output_has_full_reconstructed_target :
    ∃ b : Named (Option (Fin 2)),
      Named.BoundOutput (Named.restrictNames (Named.restrictionNames {7} {40})
        (.embed (.par (activeFrame providers) (program.compile 0)))) 0 b ∧
      Named.Structural (b.rename outputHandle)
        (Named.restrictedState {7} ⟨providers.extend payload,.nil⟩) :=
  Named.restricted_program_output providers program 0 (by decide)

abbrev localContinuation : Agent (Option (Option Empty)) := .input 8
  (.output 9 (.binary .pair (.var none)
    (.binary .pair (.var (some none)) (.var (some (some none))))) .nil)
abbrev afterLocal : Agent (Option Empty) := .input 8
  (.output 9 (.binary .pair (.var none) (.binary .pair (.var (some none)) (.name 40))) .nil)

theorem input_capture_and_local_coordinates_are_retained :
    localContinuation.subst (liftSubst (inputSubst (.name 40))) = afterLocal := rfl

theorem arbitrary_continuation_survives_scope_normalization :
    Structural
      (.newVar ((Extended.par ((Extended.active none (shiftTerm (.name 40 : Term Empty))).rename some)
        (.par (.active none (shiftTerm (.binary .pair (.var none) (.name 41))))
          (.plain localContinuation))).rename swapBinders))
      (.par (.active none (.binary .pair (.name 40) (.name 41))) (.plain afterLocal)) :=
  scope_capture_normalize (.name 40) (.binary .pair (.var none) (.name 41)) localContinuation

theorem changed_local_continuation_is_not_the_exact_result :
    localContinuation.subst (liftSubst (inputSubst (.name 40))) ≠
      (.input 8 (.output 9 (.binary .pair (.var none)
        (.binary .pair (.var (some none)) (.name 41))) .nil) : Agent (Option Empty)) := by
  intro h
  cases h

abbrev scopeState : Extended (Option Empty) :=
  .newVar ((Extended.par ((Extended.active none (shiftTerm (.name 40 : Term Empty))).rename some)
    (.par (.active none (shiftTerm (.binary .pair (.var none) (.name 41))))
      (.plain localContinuation))).rename swapBinders)
abbrev readResult : Extended (Option Empty) :=
  .par (.active none (.binary .pair (.name 40) (.name 41)))
    (.plain (.output 9 (.binary .pair (.const .one)
      (.binary .pair (.var none) (.name 40))) .nil))

theorem normalized_continuation_performs_actual_input :
    FreeStep (.par (.active none (.binary .pair (.name 40) (.name 41))) (.plain afterLocal))
      (.input 8 (.const .one)) readResult :=
  .parRight _ (.input 8 (.const .one) _)

theorem unnormalized_scope_performs_the_same_input :
    FreeStep scopeState (.input 8 (.const .one)) readResult :=
  .congr arbitrary_continuation_survives_scope_normalization
    normalized_continuation_performs_actual_input (.refl _)

end ExplainableCrypto.Helios.Symbolic.SourceProgramCaptureSPOT
