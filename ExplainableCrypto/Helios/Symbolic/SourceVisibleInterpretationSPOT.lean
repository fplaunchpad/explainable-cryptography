import ExplainableCrypto.Helios.Symbolic.SourceInterpretationCapture
import ExplainableCrypto.Helios.Symbolic.SourceInterpretationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceVisibleInterpretationSPOT
open Historical General Source Extended

abbrev wrapped : Ground := SourceInterpretationSPOT.wrapped
abbrev oldFrame := SourceAtomicOutputSPOT.oldFrame
abbrev echo : Agent (Option Empty) := .output 9 (.var none) .nil

/-- An E-equivalent emitted representative is permitted at the fresh handle. -/
theorem equivalent_capture_environment :
    (capture (.const .one : Term Nat) (.output 9 (.var 7) .nil)).Realizes
      (extendEnv (fun _ => .name 40) wrapped) (.output 9 (.name 40) .nil) :=
  capture_realizes _ _ _ (.equation (.fst _ _))

theorem incorrect_capture_value_rejected (p : Agent Empty) :
    ¬ (capture (.const .one : Term Nat) .nil).Realizes
      (extendEnv (fun _ => .name 40) (.const .zero)) p := by
  intro h
  exact zero_not_one ((capture_realizes_iff _ _ _ _ _).mp h).1

/-- The fresh emitted value and the restricted local occupy different slots. -/
theorem scope_environment_exchange :
    (fun v => extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 41)) (.name 40) (swapBinders v)) =
      extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 40)) (.name 41) :=
  extendEnv_swapBinders _ _ _

theorem omitted_scope_exchange_rejected :
    ¬ EqE (extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 41)) (.name 40) none)
      (extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 40)) (.name 41) none) := by
  intro h
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp h)

abbrev scopedSource : Extended (Fin 1) :=
  .newVar (.par (.active none (.name 40)) (.plain (.output 0 (.name 41) .nil)))
abbrev scopedTarget : Extended (Option (Fin 1)) :=
  .newVar (.par (.active none (.name 40))
    (.par (.active (some none) (.name 41)) (.plain .nil)))

theorem scoped_output_interpreted :
    ∃ m q, Agent.Visible (.output 0 (.name 41) .nil) (.output 0 m) q ∧
      scopedTarget.Realizes (extendEnv (fun _ => .name 42) m) q := by
  apply SourceAtomicOutputSPOT.output_crosses_variable_scope.realizes
  refine ⟨.name 40,.nil,.output 0 (.name 41) .nil,⟨.refl _,.refl _⟩,.refl _,?_⟩
  exact .of_parEq ((Agent.ParEq.comm _ _).trans (.zero _))

/-- Independently chosen local 40 and public value 41 realize the target. -/
theorem scoped_target_has_correct_values :
    scopedTarget.Realizes (extendEnv (fun _ => .name 42) (.name 41)) .nil := by
  refine ⟨.name 40,.nil,.nil,⟨.refl _,.refl _⟩,?_,.of_parEq (.zero _)⟩
  exact ⟨.nil,.nil,⟨.refl _,.refl _⟩,.refl _,.of_parEq (.zero _)⟩

theorem old_handle_unchanged_by_extension :
    extendEnv oldFrame.value wrapped (some (0 : Fin 1)) = .unary .pk (.name 40) ∧
    extendEnv oldFrame.value wrapped none = wrapped := ⟨rfl,rfl⟩

/-- No structural route after bound output can change an old bit handle. -/
theorem changed_old_handle_rejected (p q : Agent Empty) (c : Nat)
    (b : Extended (Option (Fin 1))) :
    ¬ (BoundOutput (frameProcess (⟨fun _ => .const .zero⟩ : Frame ∅ 1) p) c b ∧
      Structural (b.rename outputHandle) (frameProcess (⟨fun _ => .const .one⟩ : Frame ∅ 2) q)) := by
  rintro ⟨h,ht⟩
  obtain ⟨m,r,_,hv,_⟩ := frameProcess_bound_values _ _ p q h ht
  have hh := hv (Fin.castSucc (0 : Fin 1))
  rw [Frame.extend_old] at hh
  exact zero_not_one hh

/-- An actual handle recipe is received as its evaluated key, with the full
canonical target frame and an interpreted visible continuation. -/
theorem handle_recipe_input_interpreted :
    ∃ q, Agent.Visible (.input 8 echo) (.input 8 (.unary .pk (.name 40))) q ∧
      (frameProcess oldFrame (.output 9 (.unary .pk (.name 40)) .nil)).Realizes oldFrame.value q := by
  apply frameProcess_input_interpreted oldFrame (.input 8 echo) (r := .var 0)
  exact frame_visible_input_derivable oldFrame (.var 0) (.of_core (.input 8 _ echo))

theorem canonical_input_preserves_observations :
    oldFrame.StaticEq oldFrame := by
  apply frameProcess_input_staticEq oldFrame oldFrame (.input 8 echo) (.output 9 (.unary .pk (.name 40)) .nil)
  exact frame_visible_input_derivable oldFrame (.var 0) (.of_core (.input 8 _ echo))

/-- A projection wrapper can actually be emitted while its captured source
binding uses the E-equivalent bit. Literal output equality is not assumed. -/
theorem wrapped_output_realizes_bit_capture :
    ∃ m q, Agent.Visible (.output 0 wrapped .nil) (.output 0 m) q ∧
      (capture (.const .one : Ground) .nil).Realizes (extendEnv Empty.elim m) q := by
  apply (message_output 0 (.const .one : Ground) .nil).realizes
  exact Agent.EvalEq.of_equivE (.output 0 (EqE.equation (.fst _ _)).symm .nil)

abbrev proofPayload : Ground := .spk (.unary .pk (.name 40)) (.name 41) (.const .zero)
  (.ternary .penc (.unary .pk (.name 40)) (.name 41) (.const .one))

/-- Even a deliberately mismatched proof fixture is captured in full. This is
an output-semantics control, not an acceptance or security assertion. -/
theorem full_proof_capture_contents :
    (oldFrame.extend proofPayload).value 0 = .unary .pk (.name 40) ∧
    (oldFrame.extend proofPayload).value 1 =
      .spk (.unary .pk (.name 40)) (.name 41) (.const .zero)
        (.ternary .penc (.unary .pk (.name 40)) (.name 41) (.const .one)) := ⟨rfl,rfl⟩

theorem derived_full_capture_observations :
    ∃ m q, Agent.Visible (.output 0 proofPayload .nil) (.output 0 m) q ∧
      (oldFrame.extend m).StaticEq (oldFrame.extend proofPayload) ∧ Agent.EvalEq .nil q := by
  exact frameProcess_bound_staticEq oldFrame (oldFrame.extend proofPayload)
    (.output 0 proofPayload .nil) .nil (frame_output_derivable _ _ _ _) (frame_output_capture _ _ _)

/-- The actual first election publication has an interpreted captured target
at the environment extended by its actual emitted complete ballot. -/
theorem honest_publication_interpreted (swap : Bool) :
    let φ := sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .firstReceived
    let p := residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .firstReceived
    let q := residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .firstPublished
    let ballot := General.ballot SharedTallySPOT.names 0 (General.choice swap SharedTallySPOT.left SharedTallySPOT.right 0).value
    ∃ m r, Agent.Visible p (.output 0 m) r ∧
      (Extended.par ((activeFrame φ).rename some) (capture (groundTerm ballot) (groundAgent q))).Realizes
        (extendEnv φ.value m) r := by
  exact (SourceAtomicOutputSPOT.honest_publication_derivable swap).realizes _ (frameProcess_realizes _ _)

end ExplainableCrypto.Helios.Symbolic.SourceVisibleInterpretationSPOT
