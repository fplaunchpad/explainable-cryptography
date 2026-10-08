import ExplainableCrypto.Helios.Symbolic.SourceCaptureAlgebra
import ExplainableCrypto.Helios.Symbolic.SourceVariableFramePrefixSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceCapturedEquationsSPOT
open Historical General Source Extended

abbrev first : Extended (Fin 2) := .active 0 (.name 40)
abbrev second : Extended (Fin 2) := .active 1 (.name 41)
abbrev providers : Extended (Fin 2) := .par first second
abbrev values (i : Fin 2) : Ground := if i=0 then .name 40 else .name 41

private theorem providers_satisfied : providers.Satisfies values := ⟨.refl _,.refl _⟩

theorem selected_provider_keeps_full_frame : CapturedEq providers (.var 0) (.name 40) :=
  (CapturedEq.provider 0 (.name 40)).parLeft second

/-- Only the context's hole is replaced; the other old-variable occurrence
remains in the exact target syntax. -/
theorem selected_occurrence_has_actual_path :
    CapturedEq providers (.binary .pair (.var 0) (.var 0))
      (.binary .pair (.name 40) (.var 0)) :=
  selected_provider_keeps_full_frame.context (.binary .pair (.var none) (.var (some 0)))

theorem simultaneous_substitution_is_not_selective :
    (.binary .pair (.var (0 : Fin 2)) (.var 0) : Term (Fin 2)).subst (replaceVar 0 (.name 40)) ≠
      .binary .pair (.name 40) (.var 0) := by
  simp [Term.subst, replaceVar]

theorem fourth_proof_field_has_contextual_path :
    CapturedEq providers (.spk (.name 1) (.name 2) (.const .one) (.var 0))
      (.spk (.name 1) (.name 2) (.const .one) (.name 40)) :=
  (CapturedEq.refl _ _).spk (.refl _ _) (.refl _ _) selected_provider_keeps_full_frame

theorem different_provider_values_do_not_collapse : ¬ CapturedEq providers (.var 0) (.var 1) := by
  intro h
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp (h.sound providers_satisfied))

theorem actual_capture_quotient_is_nontrivial :
    Quotient.mk (capturedSetoid providers) (.var 0) ≠ Quotient.mk (capturedSetoid providers) (.var 1) :=
  fun h => different_provider_values_do_not_collapse (Quotient.exact h)

theorem provider_equations_supply_the_model :
    (captureAlgebra providers).Satisfies providers
      (fun v => Quotient.mk (capturedSetoid providers) (.var v)) :=
  FrameForest.captureAlgebra_satisfies (by trivial)

/-- The public self-equation can take another atom, so the quotient cannot
invent a structural grounding of it to a fixed literal. -/
theorem cyclic_provider_does_not_gain_ground_capture :
    ¬ CapturedEq (.active (0 : Fin 1) (.var 0)) (.var 0) (.name 40) := by
  intro h
  have he := h.sound (env := fun _ => .name 41) (EqE.refl _)
  exact (by decide : (41 : Nat) ≠ 40) ((EqE.name_iff 41 40).mp he)

open SourceVariableFramePrefixSPOT in
/-- The old public frame remains while two local providers determine the fresh
pair. Closing both locals preserves the exact outside fresh-handle coordinate. -/
theorem two_local_capture_is_structurally_grounded :
    CapturedEq raw (.var none) (.binary .pair (.const .zero) (.const .one)) := by
  have hz : CapturedEq gathered (.var (some none)) (.const .zero) :=
    ((CapturedEq.provider (some none) (.const .zero)).parRight
      (.active (some (some (some 0))) (.name 99))).parLeft inner
  have ho : CapturedEq gathered (.var none) (.const .one) :=
    ((CapturedEq.provider none (.const .one)).parLeft
      (.active (some (some none)) (.binary .pair (.var (some none)) (.var none)))).parRight _
  have hp : CapturedEq gathered (.var (some (some none)))
      (.binary .pair (.var (some none)) (.var none)) :=
    ((CapturedEq.provider (some (some none)) _).parRight (.active none (.const .one))).parRight _
  have hg := hp.trans (hz.binary ho .pair)
  have hc := CapturedEq.closeVars 2 gathered (.var none) (.binary .pair (.const .zero) (.const .one))
    (by simpa only [Term.subst,outerVar] using hg)
  exact hc.frame_structural two_local_capture_hoists_with_all_providers.1.symm

abbrev openedCapture : Extended (Option (Fin 0)) :=
  .par (.active none (.name 100)) (.plain .nil)

private theorem capture_opening :
    Named.Opens SourceFrameCompatibilitySPOT.latentPrivateCapture NameAssignment.literal
      [.base 100] openedCapture :=
  .newName (.base 40) 100 (.embed _ _) (by decide)

/-- The actual output theorem constructs its quotient solution and returns a
source structural path with an independently checked private-name value. -/
theorem actual_output_derives_ground_structural_capture :
    ∃ m : Ground, EqE m (.name 100) ∧ CapturedEq openedCapture.frameOf (.var none) (groundTerm m) := by
  obtain ⟨m,hm⟩ :=
    SourceFrameCompatibilitySPOT.latent_private_name_has_actual_output.opened_capture_ground
      SourceFrameCompatibilitySPOT.latent_private_name_can_be_retained_in_old_policy capture_opening
  have hv := hm.sound (env := fun _ => .name 100) ⟨.refl _,True.intro⟩
  refine ⟨m,?_,hm⟩
  simpa only [Term.subst,groundTerm_eval] using hv.symm

end ExplainableCrypto.Helios.Symbolic.SourceCapturedEquationsSPOT
