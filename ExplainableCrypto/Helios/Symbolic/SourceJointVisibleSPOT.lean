import ExplainableCrypto.Helios.Symbolic.SourceElectionJointVisible
import ExplainableCrypto.Helios.Symbolic.SourceJointOpeningSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceJointVisibleSPOT
open Historical General Source SourceVisibleInvariantSPOT

abbrev inputSource : ScopedState {40} 1 := ⟨φ,inputCode⟩
abbrev inputTarget : ScopedState {40} 1 := ⟨φ,inputResult⟩

theorem actual_private_continuation_input :
    Named.FreeStep (Named.restrictedState {8} inputSource) (.input 7 (.var 0))
      (Named.restrictedState {8} inputTarget) :=
  Named.restricted_input_derivable inputSource inputTarget 7 (.var 0)
    (.input φ 7 (.var 0) (by decide) (by trivial) (.of_core (.input 7 (.name 40) echo)))

theorem public_input_retains_joint :
    Named.JointOpening (Named.restrictedState {8} inputTarget) (Named.restrictedState {8} inputTarget) :=
  (Named.restrictedState_jointOpening inputSource).public_input_target actual_private_continuation_input
    (by trivial) input_result_is_deterministic

theorem public_input_has_exact_original_label :
    ∃ q, Agent.Visible inputCode (.input 7 (φ.eval (.var 0))) q :=
  (Named.restrictedState_jointOpening inputSource).public_input_step actual_private_continuation_input (by trivial)

theorem input_target_private_output_stays_blocked (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput (Named.restrictedState {8} inputTarget) 8 b :=
  public_input_retains_joint.private_bound_blocked inputTarget 8 (by decide)

abbrev outputTarget : ScopedState {40} 2 := ⟨φ.extend payload,continuation⟩
noncomputable abbrev rawCapture := Named.restrictedCapture {9} φ payload continuation

theorem actual_scoped_full_capture : Named.BoundOutput (Named.restrictedState {9} canonical) 8 rawCapture :=
  (Named.BoundOutput.embed actual_full_output).restrictNames (Named.restrictionNames {9} {40})
    ((Named.output_restriction_fresh_iff 8).mpr (by decide))

theorem full_capture_retains_joint :
    Named.JointOpening (rawCapture.rename Extended.outputHandle) (Named.restrictedState {9} outputTarget) :=
  (Named.restrictedState_jointOpening canonical).output_target actual_scoped_full_capture full_output_is_deterministic

theorem full_output_has_original_channel : ∃ m q, Agent.Visible outputCode (.output 8 m) q :=
  (Named.restrictedState_jointOpening canonical).output_step actual_scoped_full_capture

theorem output_target_private_input_stays_blocked (b : Named (Fin 2)) :
    ¬ Named.FreeStep (rawCapture.rename Extended.outputHandle) (.input 9 (.var 1)) b :=
  full_capture_retains_joint.private_free_blocked outputTarget _ (by decide)

theorem complete_fresh_value_not_truncated (q : Agent Empty) :
    ¬ capture.Realizes (extendEnv φ.value wrongFourth) q := wrong_fourth_field_is_rejected q

theorem complete_old_value_not_overwritten (q : Agent Empty) :
    ¬ capture.Realizes (extendEnv (fun _ => .name 42) payload) q := wrong_old_value_is_rejected q

theorem unequal_outputs_refute_determinism :
    ¬ (∀ c m q n r, Agent.Visible competing (.output c m) q → Agent.Visible competing (.output c n) r →
      EqE m n ∧ Agent.EvalEq q r) := output_determinism_cannot_drop_payloads

abbrev alphaFrame : Frame {40} 1 := ⟨fun _ => .unary .pk (.name 40)⟩
abbrev alphaCode : Agent Empty := .input 0 (.output 0 (.var none) .nil)
abbrev alphaCanonical : ScopedState {40} 1 := ⟨alphaFrame,alphaCode⟩
abbrev alphaRaw := SourceOperationalPrenexSPOT.alphaSource
abbrev alphaTarget := SourceOperationalPrenexSPOT.alphaTarget

theorem alpha_raw_is_canonical_representative :
    Named.Structural (Named.restrictedState ∅ alphaCanonical) alphaRaw := by
  have he : Extended.Structural (Extended.frameProcess alphaFrame alphaCode)
      (SourceInputAlphaBoundary.keyAndInput 40) := .parLeft _ (.zero _)
  simpa [Named.restrictedState,Named.restrictionNames,Named.restrictNames,alphaRaw,
    SourceOperationalPrenexSPOT.alphaSource,alphaCanonical] using Named.Structural.newName (.base 40) (.embed he)

theorem alpha_raw_has_joint_partner : Named.JointOpening alphaRaw (Named.restrictedState ∅ alphaCanonical) :=
  alpha_raw_is_canonical_representative.jointOpening alphaCanonical

theorem old_private_literal_is_actual_input : Named.FreeStep alphaRaw (.input 0 (.name 40)) alphaTarget :=
  SourceInputAlphaBoundary.old_literal_input_after_alpha

theorem old_private_literal_is_not_originally_public : ¬ (Term.name 40 : Recipe 1).Public {40} := by
  simp [Term.Public]

theorem alpha_input_is_deterministic (c : Nat) (m : Ground) (p q : Agent Empty)
    (hp : Agent.Visible alphaCode (.input c m) p) (hq : Agent.Visible alphaCode (.input c m) q) : Agent.EvalEq p q := by
  apply Agent.EvalEq.of_parEq
  apply Agent.visible_input_deterministic hp hq
  intro a b ha hb
  simp [alphaCode,Agent.threads,Agent.threadList] at ha hb
  exact ha.2.trans hb.2.symm

/-- The formerly private literal is accepted with its exact original label,
under one derived fresh policy shared by both canonical partners. -/
theorem alpha_input_retains_joint_under_common_fresh_policy :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      Named.Structural (Named.restrictedState ∅ alphaCanonical)
        (Named.restrictedState ((∅ : Finset Nat).image k) (alphaCanonical.mapNames e k)) ∧
      Named.Structural (Named.restrictedState ∅ alphaCanonical)
        (Named.restrictedState ((∅ : Finset Nat).image k) (alphaCanonical.mapNames e k)) ∧
      (Term.name 40 : Recipe 1).Public (({40} : Finset Nat).image e) ∧ k 0 = 0 ∧
      (alphaFrame.mapNames e).StaticEq (alphaFrame.mapNames e) ∧
      Named.JointOpening alphaRaw (Named.restrictedState ((∅ : Finset Nat).image k) (alphaCanonical.mapNames e k)) ∧
      Named.JointOpening alphaRaw (Named.restrictedState ((∅ : Finset Nat).image k) (alphaCanonical.mapNames e k)) ∧
      ScopedStep ((∅ : Finset Nat).image k) (({40} : Finset Nat).image e) (alphaCanonical.mapNames e k)
        (.input 0 (.name 40)) ⟨alphaFrame.mapNames e,q⟩ ∧
      Named.JointOpening alphaTarget (Named.restrictedState ((∅ : Finset Nat).image k) ⟨alphaFrame.mapNames e,q⟩) :=
  alpha_raw_has_joint_partner.common_fresh_input alphaCanonical alphaCanonical alpha_raw_has_joint_partner
    (.refl _) old_private_literal_is_actual_input alpha_input_is_deterministic

theorem complete_fourth_field_is_observed :
    SourceName.base 48 ∈ (Extended.FreeLabel.input 0 SourceOperationalPrenexSPOT.proofRecipe).nameSupport :=
  SourceOperationalPrenexSPOT.fourth_field_in_label_support

theorem moving_fourth_field_cannot_preserve_label :
    (Extended.FreeLabel.input 0 SourceOperationalPrenexSPOT.proofRecipe).mapNames (Equiv.swap 48 50) id ≠
      .input 0 SourceOperationalPrenexSPOT.proofRecipe := SourceOperationalPrenexSPOT.fourth_field_renaming_cannot_fix_label

theorem unrelated_names_preserve_complete_input :
    (Extended.FreeLabel.input 0 SourceOperationalPrenexSPOT.proofRecipe).mapNames (Equiv.swap 40 50) id =
      .input 0 SourceOperationalPrenexSPOT.proofRecipe := SourceOperationalPrenexSPOT.unrelated_name_permutation_fixes_complete_label

/-- Both vote worlds execute the actual first publication and retain the full
joint relation at firstPublished on two public handles. -/
theorem actual_first_publication_reaches_joint_phase (swap : Bool) :
    ∃ b : Named (Option (Fin 1)),
      Named.BoundOutput (SourceTargetInvariantSPOT.raw swap .firstReceived) Channels.canonical.broadcast b ∧
      PhaseJointOpening SourceTargetInvariantSPOT.ens swap SourceTargetInvariantSPOT.left
        SourceTargetInvariantSPOT.right 0 Channels.canonical .firstPublished (b.rename Extended.outputHandle) := by
  have hp := (Publication.first (ns := SourceTargetInvariantSPOT.ens) (swap := swap)
    (left := SourceTargetInvariantSPOT.left) (right := SourceTargetInvariantSPOT.right) (extra := 0)).scoped
    Channels.canonical Channels.canonical_fresh
  obtain ⟨m,hm,_⟩ := Named.restricted_output_derivable _ _ _ hp.1
  obtain ⟨handle,value,next,hpub,_,_,ht⟩ := source_joint_output_next SourceTargetInvariantSPOT.ens swap
    SourceTargetInvariantSPOT.left SourceTargetInvariantSPOT.right 0 Channels.canonical Channels.canonical_fresh
    .firstReceived (by trivial) (Named.restrictedState_jointOpening _) hm
  cases hpub
  exact ⟨_,hm,ht⟩

theorem publication_grows_the_actual_domain :
    Process.Phase.firstReceived.handles + 1 = Process.Phase.firstPublished.handles :=
  (Publication.first (ns := SourceTargetInvariantSPOT.ens) (swap := false)
    (left := SourceTargetInvariantSPOT.left) (right := SourceTargetInvariantSPOT.right) (extra := 0)).next_handles

end ExplainableCrypto.Helios.Symbolic.SourceJointVisibleSPOT
