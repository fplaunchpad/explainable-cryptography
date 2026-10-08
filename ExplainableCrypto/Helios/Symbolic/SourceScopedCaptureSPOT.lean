import ExplainableCrypto.Helios.Symbolic.SourceScopedCaptureFrames
import ExplainableCrypto.Helios.Symbolic.SourceRecipeCaptureSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceScopedCaptureSPOT
open Historical General Source Extended

abbrev providers : Frame {40} 2 := SourceRecipeCaptureSPOT.providers
abbrev program : ScopedTermProgram (Fin 2) := .letTerm (.var 0)
  (.newName 50 (.letTerm (.binary .pair (.var none) (.name 50))
    (.newName 51 (.result (.spk (.var (some none)) (.var none) (.const .one)
      (.binary .pair (.name 51) (.var none)))))))
abbrev payload : Ground := .spk (.name 40) (.binary .pair (.name 40) (.name 50)) (.const .one)
  (.binary .pair (.name 51) (.binary .pair (.name 40) (.name 50)))
abbrev wrongPayload : Ground := .spk (.name 40) (.binary .pair (.name 40) (.name 50)) (.const .one)
  (.binary .pair (.name 52) (.binary .pair (.name 40) (.name 50)))

/-- Literal raw Scope target: name 50 stays between the two locals and name 51
stays inside both; the captured active variable is outside both locals. -/
abbrev rawTarget : Named (Option (Fin 2)) := .newVar
  (.par (.embed (.active none (.var (some (some 0)))))
    (.newName (.base 50) (.newVar
      (.par (.embed (.active none (.binary .pair (.var (some none)) (.name 50))))
        (.newName (.base 51) (.embed
          (.par (.active (some (some none))
            (.spk (.var (some none)) (.var none) (.const .one)
              (.binary .pair (.name 51) (.var none)))) (.plain .nil))))))))

abbrev finalFrame : Frame ({40} ∪ program.names.toFinset) 3 :=
  (providers.extend payload).withPolicy ({40} ∪ program.names.toFinset)
noncomputable abbrev namedTarget : Named (Fin 3) :=
  (Named.restrictNames (Named.restrictionNames {7} {40})
    (.par (.embed ((activeFrame providers).rename some)) rawTarget)).rename outputHandle

theorem program_names_are_exact : program.names = [50,51] := rfl

theorem interleaved_scopes_are_safe_to_hoist : program.Hoistable := by
  simp [ScopedTermProgram.Hoistable,ScopedTermProgram.names,Term.nameSupport]

theorem program_names_avoid_every_old_provider : ∀ n ∈ program.names, n ∉ providers.nameSupport := by
  intro n hn
  simp only [program_names_are_exact,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl <;> decide

theorem original_output_retains_literal_scope_positions : program.capture = rawTarget := rfl

theorem original_scoped_output_has_that_exact_target : Named.BoundOutput (program.compile 0) 0 rawTarget :=
  program.compile_output_capture 0

theorem raw_capture_has_actual_hoisting_path :
    Named.Structural rawTarget
      (Named.restrictNames [.base 50,.base 51] (.embed program.erase.capture)) :=
  program.capture_hoist interleaved_scopes_are_safe_to_hoist

theorem computed_payload_keeps_both_private_names : providers.eval program.erase.value = payload := rfl

theorem full_private_policy_is_exact : ({40} ∪ program.names.toFinset) = ({40,50,51} : Finset Nat) := by decide

theorem complete_canonical_reconstruction :
    Named.Structural namedTarget (Named.restrictedState {7} ⟨finalFrame,.nil⟩) :=
  Named.restricted_scoped_program_capture_normalize providers program interleaved_scopes_are_safe_to_hoist
    program_names_avoid_every_old_provider

theorem full_frame_presentation_includes_program_names : namedTarget.RepresentsFrame {7} finalFrame :=
  Named.restricted_scoped_program_capture_represents providers program interleaved_scopes_are_safe_to_hoist
    program_names_avoid_every_old_provider

theorem full_frame_static_observation_is_available :
    Named.StaticEq namedTarget (Named.restrictedState {7} ⟨finalFrame,.nil⟩) :=
  .of_presentations full_frame_presentation_includes_program_names (Named.restrictedState_represents _) (.refl _)

theorem full_provider_values_and_capture_remain_explicit :
    finalFrame.value 0 = .name 40 ∧ finalFrame.value 1 = .name 41 ∧ finalFrame.value 2 = payload := by decide

theorem actual_output_reconstructs_the_full_combined_policy :
    ∃ b : Named (Option (Fin 2)),
      Named.BoundOutput (Named.restrictNames (Named.restrictionNames {7} {40})
        (.par (.embed (activeFrame providers)) (program.compile 0))) 0 b ∧
      Named.Structural (b.rename outputHandle) (Named.restrictedState {7} ⟨finalFrame,.nil⟩) :=
  Named.restricted_scoped_program_output providers program interleaved_scopes_are_safe_to_hoist
    program_names_avoid_every_old_provider 0 (by decide)

theorem changed_private_literal_is_E_distinct_in_fixed_coordinates : ¬ EqE payload wrongPayload := by
  intro h
  have h4 := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp h).2.2.2
  have hn := ((EqE.pair_iff _ _ _ _).mp h4).1
  exact (by decide : (51 : Nat) ≠ 52) ((EqE.name_iff 51 52).mp hn)

/-- Omitting program names would wrongly admit a literal private nonce in the
recipe policy. The newly exported handle itself remains a public recipe. -/
theorem omitted_program_policy_would_admit_private_literal :
    (Term.name 50 : Recipe 3).Public {40} ∧
    ¬ (Term.name 50 : Recipe 3).Public ({40} ∪ program.names.toFinset) ∧
    (Term.var 2 : Recipe 3).Public ({40} ∪ program.names.toFinset) := by
  change (50 ∉ ({40} : Finset Nat)) ∧ ¬ (50 ∉ ({40} ∪ program.names.toFinset)) ∧ True
  decide

abbrev unsafeLocal : ScopedTermProgram (Fin 2) :=
  .letTerm (.name 50) (.newName 50 (.result (.var none)))

theorem later_name_cannot_capture_the_local_provider : ¬ unsafeLocal.Hoistable := by
  intro h
  exact h.2 50 (by simp [ScopedTermProgram.names]) (by simp [Term.nameSupport])

theorem failed_hoisting_does_not_block_original_output :
    Named.BoundOutput (unsafeLocal.compile 0) 0 unsafeLocal.capture := unsafeLocal.compile_output_capture 0

abbrev providerCollision : ScopedTermProgram (Fin 2) := .newName 40 (.result (.var 0))

theorem program_hoisting_alone_does_not_protect_the_old_frame :
    providerCollision.Hoistable ∧ ¬ (∀ n ∈ providerCollision.names, n ∉ providers.nameSupport) := by
  refine ⟨True.intro,?_⟩
  intro h
  exact h 40 (by simp [ScopedTermProgram.names]) (by decide)

theorem provider_collision_still_has_an_original_output :
    Named.BoundOutput (.par (.embed (activeFrame providers)) (providerCollision.compile 0)) 0
      (.par (.embed ((activeFrame providers).rename some)) providerCollision.capture) :=
  .parRight _ (providerCollision.compile_output_capture 0)

abbrev repeatedName : ScopedTermProgram (Fin 2) := .newName 50 (.newName 50 (.result (.name 50)))

theorem repeated_program_names_have_one_policy_entry :
    repeatedName.names = [50,50] ∧ ({40} ∪ repeatedName.names.toFinset) = ({40,50} : Finset Nat) := by decide

theorem repeated_private_scopes_have_actual_complete_presentation :
    (((Named.restrictNames (Named.restrictionNames {7} {40})
      (.par (.embed ((activeFrame providers).rename some)) repeatedName.capture)).rename outputHandle)).RepresentsFrame
      {7} ((providers.extend (.name 50)).withPolicy ({40} ∪ repeatedName.names.toFinset)) := by
  apply Named.restricted_scoped_program_capture_represents providers repeatedName True.intro
  intro n hn
  simp only [ScopedTermProgram.names,List.mem_cons,List.not_mem_nil,or_false,or_self] at hn
  subst n
  decide

theorem private_base_scope_does_not_hide_same_numbered_channel :
    Named.BoundOutput
      (.newName (.base 50) (.embed (.plain (.output 50 (.name 50) .nil))) : Named Empty) 50
      (.newName (.base 50) (.embed (Extended.capture (.name 50) .nil))) :=
  (ScopedTermProgram.newName 50 (.result (.name 50)) : ScopedTermProgram Empty).compile_output_capture 50

end ExplainableCrypto.Helios.Symbolic.SourceScopedCaptureSPOT
