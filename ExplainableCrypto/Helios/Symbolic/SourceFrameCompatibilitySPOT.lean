import ExplainableCrypto.Helios.Symbolic.SourceIndependentFrameCompatibility
import ExplainableCrypto.Helios.Symbolic.SourceFrameEquationActions
import ExplainableCrypto.Helios.Symbolic.SourceNamedStaticSPOT
import ExplainableCrypto.Helios.Symbolic.SourcePolicyPaddingSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceFrameCompatibilitySPOT
open Historical General Source

def distinct : Frame {40,41} 2 := ⟨fun i => if i=0 then .name 40 else .name 41⟩
def shared : Frame {40,41} 2 := ⟨fun _ => .name 40⟩

theorem identity_assignment_is_a_solution :
    (Named.canonicalFrame ∅ distinct).Models id distinct.value := Named.canonicalFrame_models distinct

/-- Colliding atom assignments are intentionally admitted by the constraint
instrumentation. This one equates two originally distinct exported atoms. -/
theorem one_colliding_solution_equates_distinct_handles :
    (Named.canonicalFrame ∅ distinct).Models id shared.value ∧
      EqE (shared.eval (.var 0)) (shared.eval (.var 1)) := by
  refine ⟨?_,.refl _⟩
  apply (Named.canonicalFrame_models_iff distinct shared.value).mpr
  refine ⟨Function.update id 41 40,?_,?_⟩
  · intro n hn
    have he : n ≠ 41 := fun he => hn (by simp [he])
    simp [Function.update_of_ne he]
  · intro i
    fin_cases i <;> exact .refl _

theorem distinct_handles_are_not_universally_equal :
    ¬ (Named.canonicalFrame ∅ distinct).ValidEquation (.var 0) (.var 1) := by
  intro h
  have he := h distinct.value identity_assignment_is_a_solution
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp he)

theorem shared_handles_are_universally_equal :
    (Named.canonicalFrame ∅ shared).ValidEquation (.var 0) (.var 1) :=
  (Named.canonicalFrame_validEquation_iff shared (.var 0) (.var 1) trivial trivial).mpr (.refl _)

theorem collapsing_private_atoms_changes_observations :
    ¬ Named.StaticEq (Named.canonicalFrame ∅ distinct) (Named.canonicalFrame ∅ shared) := by
  intro h
  exact distinct_handles_are_not_universally_equal
    ((h.validEquation (.var 0) (.var 1)).mpr shared_handles_are_universally_equal)

abbrev rawPrivate : Named (Fin 1) := .newName (.base 40) (.embed (.active 0 (.name 40)))
abbrev renamedPrivate : Named (Fin 1) := .newName (.base 50) (.embed (.active 0 (.name 50)))

private theorem alpha_path : Named.Structural rawPrivate renamedPrivate := by
  simpa only [Named.mapNames,Extended.mapNames,Term.mapNames,Equiv.swap_apply_left] using
    Named.Structural.alphaBase (.embed (.active (0 : Fin 1) (.name 40))) 40 50 (by decide)

theorem alpha_preserves_all_equation_solutions (env : Fin 1 → Ground) :
    rawPrivate.Models id env ↔ renamedPrivate.Models id env := alpha_path.models id env

theorem renamed_binder_keeps_old_solution : renamedPrivate.Models id (fun _ => .name 40) :=
  (alpha_preserves_all_equation_solutions _).mp ⟨40,.refl _⟩

theorem one_literal_solution_is_not_a_public_observation :
    rawPrivate.Models id (fun _ => .name 40) ∧
      ¬ rawPrivate.ValidEquation (.var 0) (.name 40) := by
  refine ⟨⟨40,.refl _⟩,?_⟩
  intro h
  have he := h (fun _ => .name 41) ⟨41,.refl _⟩
  exact (by decide : (41 : Nat) ≠ 40) ((EqE.name_iff 41 40).mp he)

theorem free_name_stays_observable :
    (Named.embed (.active (0 : Fin 1) (.name 40))).ValidEquation (.var 0) (.name 40) :=
  fun _ h => h

abbrev inconsistent : Named (Fin 1) :=
  .par (.embed (.active 0 (.const .zero))) (.embed (.active 0 (.const .one)))

theorem inconsistent_frame_has_no_solution (env : Fin 1 → Ground) :
    ¬ inconsistent.Models id env := fun h => zero_not_one (h.1.symm.trans h.2)

theorem vacuous_equations_do_not_supply_presentation :
    inconsistent.ValidEquation (.const .zero) (.const .one) ∧
      ∀ (hidden policy : Finset Nat) (φ : Frame policy 1), ¬ inconsistent.RepresentsFrame hidden φ := by
  refine ⟨fun env h => (inconsistent_frame_has_no_solution env h).elim,?_⟩
  intro hidden policy φ h
  exact inconsistent_frame_has_no_solution φ.value h.models

abbrev dependent : Named (Fin 1) := .newVar
  (.par (.embed (.active none (.name 40))) (.embed (.active (some 0) (.var none))))

theorem active_local_chain_has_expected_solution : dependent.Models id (fun _ => .name 40) :=
  ⟨.name 40,.refl _,.refl _⟩

theorem active_local_chain_rejects_wrong_export : ¬ dependent.Models id (fun _ => .name 41) := by
  rintro ⟨m,hm,hx⟩
  exact (by decide : (41 : Nat) ≠ 40) ((EqE.name_iff 41 40).mp (hx.trans hm))

theorem full_fourth_field_remains_in_constraint :
    (Named.embed (.active (0 : Fin 1)
      (.spk (.name 1) (.name 2) (.const .one) (.name 99)))).Models id
        (fun _ => .spk (.name 1) (.name 2) (.const .one) (.name 99)) := .refl _

theorem changed_public_bit_has_no_static_witness :
    ¬ Named.StaticEq (Named.canonicalFrame ∅ SourcePolicyPaddingSPOT.zeros)
      (Named.canonicalFrame ∅ SourcePolicyPaddingSPOT.ones) := by
  intro h
  have hz : (Named.canonicalFrame ∅ SourcePolicyPaddingSPOT.zeros).ValidEquation (.var 0) (.const .zero) :=
    (Named.canonicalFrame_validEquation_iff SourcePolicyPaddingSPOT.zeros
      (.var 0) (.const .zero) trivial trivial).mpr (.refl _)
  have ho := (h.validEquation (.var 0) (.const .zero)).mp hz
  exact zero_not_one (ho _ (Named.canonicalFrame_models SourcePolicyPaddingSPOT.ones)).symm

theorem independent_presentations_are_compatible
    (a : Named (Fin 2)) (φ ψ : Frame {40,41,42} 2)
    (ha : a.RepresentsFrame {7} φ) (hb : a.RepresentsFrame {8,9} ψ) : φ.StaticEq ψ :=
  ha.compatible hb

/-- Compose actual source witnesses with different hidden channel policies and
different ground syntax at the two ends. -/
theorem actual_three_frame_composition :
    Named.StaticEq (Named.canonicalFrame {7} SourcePolicyPaddingSPOT.left)
      (Named.canonicalFrame {9} SourcePolicyPaddingSPOT.leftExpanded) := by
  have h₁ : Named.StaticEq (Named.canonicalFrame {7} SourcePolicyPaddingSPOT.left)
      (Named.canonicalFrame {8} SourcePolicyPaddingSPOT.left) :=
    .of_presentations (Named.canonicalFrame_represents _)
      ((Named.canonicalFrame_represents _).structural
        (Named.canonicalFrame_hidden_irrelevant _ {7} {8})) (.refl _)
  have h₂ : Named.StaticEq (Named.canonicalFrame {8} SourcePolicyPaddingSPOT.left)
      (Named.canonicalFrame {9} SourcePolicyPaddingSPOT.leftExpanded) :=
    .of_presentations (Named.canonicalFrame_represents _)
      ((Named.canonicalFrame_represents _).structural
        (Named.canonicalFrame_hidden_irrelevant _ {8} {9}))
      SourcePolicyPaddingSPOT.different_syntax_equal_observations
  exact h₁.trans h₂

theorem full_literal_tests_transfer_after_composition :
    (Named.canonicalFrame {7} SourcePolicyPaddingSPOT.left).ValidEquation SourceNamedStaticSPOT.fullTest (.var 0) ↔
      (Named.canonicalFrame {9} SourcePolicyPaddingSPOT.leftExpanded).ValidEquation SourceNamedStaticSPOT.fullTest (.var 0) :=
  actual_three_frame_composition.validEquation _ _

theorem protocol_static_witness_composes :
    Named.StaticEq
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical (.done [])))
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical (.done []))) :=
  SourceNamedStaticSPOT.completed_zero_extra_named_staticEq.trans
    SourceNamedStaticSPOT.completed_zero_extra_named_staticEq.symm

abbrev beforeOutput : Named (Fin 1) := .embed
  (.par (.active 0 (.const .zero)) (.plain (.output 0 (.const .one) .nil)))
abbrev afterOutput : Named (Option (Fin 1)) := .embed
  (.par (.active (some 0) (.const .zero)) (Extended.capture (.const .one) .nil))

theorem actual_publication_has_fresh_handle : Named.BoundOutput beforeOutput 0 afterOutput :=
  .embed (Extended.message_output_in_context (.active 0 (.const .zero)) 0 (.const .one) .nil)

theorem old_equation_survives_actual_publication :
    beforeOutput.ValidEquation (.var 0) (.const .zero) ∧
      afterOutput.ValidEquation (.var (some 0)) (.const .zero) := by
  have h : beforeOutput.ValidEquation (.var 0) (.const .zero) := fun _ hm => hm.1
  exact ⟨h,(actual_publication_has_fresh_handle.old_validEquation_iff _ _).mp h⟩

theorem fresh_output_adds_its_own_equation :
    afterOutput.ValidEquation (.var none) (.const .one) := fun _ hm => hm.2.1

theorem fresh_output_is_not_the_old_zero :
    ¬ afterOutput.ValidEquation (.var none) (.const .zero) := by
  intro h
  have he := h (extendEnv (fun _ => .const .zero) (.const .one))
    ⟨.refl _,.refl _,True.intro⟩
  exact zero_not_one he.symm

/-- A private atom can occur only in the live process, outside the old frame. -/
abbrev latentPrivateOutput : Named (Fin 0) :=
  .newName (.base 40) (.embed (.plain (.output 0 (.name 40) .nil)))
abbrev latentPrivateCapture : Named (Option (Fin 0)) :=
  .newName (.base 40) (.embed (.par (.active none (.name 40)) (.plain .nil)))
abbrev latentPrivateTarget : Named (Fin 1) := latentPrivateCapture.rename Extended.outputHandle
abbrev emptyPublicFrame : Frame ∅ 0 := ⟨Fin.elim0⟩
abbrev emptyPrivateFrame : Frame {40} 0 := ⟨Fin.elim0⟩
abbrev capturedPrivateFrame : Frame {40} 1 := ⟨fun _ => .name 40⟩

theorem latent_private_name_has_actual_output :
    Named.BoundOutput latentPrivateOutput 0 latentPrivateCapture :=
  .scopeName (.base 40) (by decide) (.embed (Extended.message_output 0 (.name 40) .nil))

theorem latent_private_name_is_absent_from_old_frame_policy :
    latentPrivateOutput.RepresentsFrame ∅ emptyPublicFrame := by
  simp only [Named.RepresentsFrame,Named.canonicalFrame,Named.restrictionNames,
    Finset.toList_empty,List.map_nil,List.append_nil,Named.restrictNames,List.foldr_nil]
  exact .nameZero _

theorem latent_private_name_can_be_retained_in_old_policy :
    latentPrivateOutput.RepresentsFrame ∅ emptyPrivateFrame := by
  simp only [Named.RepresentsFrame,Named.canonicalFrame,Named.restrictionNames,
    Finset.toList_singleton,Finset.toList_empty,List.map_cons,List.map_nil,List.append_nil,
    Named.restrictNames,List.foldr_cons,List.foldr_nil]
  exact .refl _

theorem latent_private_output_recloses_to_empty_policy :
    (Named.newVar latentPrivateCapture).RepresentsFrame ∅ emptyPublicFrame :=
  latent_private_name_is_absent_from_old_frame_policy.bound_reclose latent_private_name_has_actual_output

theorem latent_private_capture_has_full_private_presentation :
    latentPrivateTarget.RepresentsFrame ∅ capturedPrivateFrame := by
  simp only [Named.RepresentsFrame,Named.canonicalFrame,Named.restrictionNames,
    Finset.toList_singleton,Finset.toList_empty,List.map_cons,List.map_nil,List.append_nil,
    Named.restrictNames,List.foldr_cons,List.foldr_nil]
  exact .refl _

/-- These are two atom assignments, not two values for a local variable.
Local rigidity therefore does not rule out this private-policy distinction. -/
theorem latent_private_capture_models_every_atom (v : Nat) :
    latentPrivateTarget.Models id (fun _ => .name v) := by
  change ∃ k : Nat, EqE (.name v : Ground) (.name k) ∧ True
  exact ⟨v,.refl _,True.intro⟩

/-- Empty base policy fails for every candidate value and every channel policy,
not just for a deliberately wrong literal target. -/
theorem latent_private_capture_has_no_empty_policy (hidden : Finset Nat) (φ : Frame ∅ 1) :
    ¬ latentPrivateTarget.RepresentsFrame hidden φ := by
  intro h
  have hv (v : Nat) : EqE (.name v : Ground) (φ.value 0) := by
    have hm := (Named.Structural.models h id (fun _ => .name v)).mp
      ((Named.models_frameOf latentPrivateTarget id _).mpr (latent_private_capture_models_every_atom v))
    obtain ⟨ρ,hfix,hval⟩ := (Named.canonicalFrame_models_iff φ _).mp hm
    have hi : ρ = id := funext (fun n => hfix n (by simp))
    simpa only [hi,Term.mapNames_id] using hval 0
  have he := (EqE.name_iff 40 41).mp ((hv 40).trans (hv 41).symm)
  exact (by decide : (40 : Nat) ≠ 41) he

/-- Actual frame presentation and exact output reclosure do not establish
same-policy presentation of the newly public handle. -/
theorem frame_only_same_policy_output_reconstruction_refuted :
    latentPrivateOutput.RepresentsFrame ∅ emptyPublicFrame ∧
    Named.BoundOutput latentPrivateOutput 0 latentPrivateCapture ∧
    (Named.newVar latentPrivateCapture).RepresentsFrame ∅ emptyPublicFrame ∧
    ¬ ∃ (hidden : Finset Nat) (φ : Frame ∅ 1), latentPrivateTarget.RepresentsFrame hidden φ :=
  ⟨latent_private_name_is_absent_from_old_frame_policy,latent_private_name_has_actual_output,
    latent_private_output_recloses_to_empty_policy,fun ⟨hidden,φ,h⟩ =>
      latent_private_capture_has_no_empty_policy hidden φ h⟩

end ExplainableCrypto.Helios.Symbolic.SourceFrameCompatibilitySPOT
