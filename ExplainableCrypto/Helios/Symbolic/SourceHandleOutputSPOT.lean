import ExplainableCrypto.Helios.Symbolic.SourceHandleOutputDerivation
import ExplainableCrypto.Helios.Symbolic.SourceVisibleInvariantSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceHandleOutputSPOT
open Historical General Source
open SourceVisibleInvariantSPOT (payload wrongFourth continuation outputCode full_output_is_deterministic)

abbrev φ : Frame {40} 2 := ⟨Fin.cases payload (fun _ => wrongFourth)⟩
noncomputable abbrev canonical : Named (Fin 2) := Named.restrictedState {7} ⟨φ,outputCode⟩
noncomputable abbrev target : Named (Fin 2) := Named.restrictedState {7} ⟨φ,continuation⟩

/-- Figure 3 Out-Atom exposes the first old handle; its full private-containing
SPK value and the other old handle remain in the original two-entry frame. -/
theorem actual_old_handle_output : Named.FreeStep canonical (.output 8 0) target :=
  Named.restricted_handle_output_derivable φ 8 0 continuation (by decide)

abbrev extRaw : Extended (Fin 2) := .par (Extended.frameProcess φ outputCode) (.plain .nil)
abbrev extTarget : Extended (Fin 2) := .par (Extended.frameProcess φ continuation) (.plain .nil)

theorem actual_extended_handle_output : Extended.FreeStep extRaw (.output 8 0) extTarget :=
  .parLeft _ (Extended.frame_handle_output_derivable φ 8 0 continuation)

theorem old_handle_target_has_complete_class :
    extTarget.SameRealizations (Extended.frameProcess φ continuation) :=
  actual_extended_handle_output.output_sameRealizations_target φ outputCode continuation (Extended.Structural.zero _).sameRealizations
    (fun m q _ h => (full_output_is_deterministic m q h).2)

theorem old_handle_target_keeps_joint_opening : Named.JointOpening target target :=
  (Named.restrictedState_jointOpening (⟨φ,outputCode⟩ : ScopedState {40} 2)).handle_output_target
    actual_old_handle_output (fun m q _ h => (full_output_is_deterministic m q h).2)

theorem full_old_handle_value_is_observed :
    ∃ m q, EqE payload m ∧ Agent.Visible outputCode (.output 8 m) q :=
  (Named.restrictedState_jointOpening (⟨φ,outputCode⟩ : ScopedState {40} 2)).handle_output_step actual_old_handle_output

private theorem fields_differ : ¬ EqE wrongFourth payload := by
  intro h
  have he := (EqE.spk_iff _ _ _ _ _ _ _ _).mp h
  have hn := (EqE.name_iff 98 99).mp he.2.2.2
  cases hn

/-- Changing only which existing handle is emitted changes the fourth field;
no raw target, including an arbitrary structural representative, can hide it. -/
theorem other_handle_cannot_label_this_output (b : Named (Fin 2)) :
    ¬ Named.FreeStep canonical (.output 8 1) b := by
  intro h
  obtain ⟨m,q,hm,hq⟩ := (Named.restrictedState_jointOpening
    (⟨φ,outputCode⟩ : ScopedState {40} 2)).handle_output_step h
  exact fields_differ (hm.trans (full_output_is_deterministic m q hq).1)

theorem changed_emitted_handle_rejected (q : Agent Empty) :
    ¬ extTarget.Realizes (fun _ => wrongFourth) q := by
  intro h
  have hv := ((Extended.frameProcess_realizes_iff φ continuation _ q).mp
    ((old_handle_target_has_complete_class _ q).mp h)).1 0
  exact fields_differ hv

theorem changed_unemitted_handle_rejected (q : Agent Empty) :
    ¬ extTarget.Realizes (fun _ => payload) q := by
  intro h
  have hv := ((Extended.frameProcess_realizes_iff φ continuation _ q).mp
    ((old_handle_target_has_complete_class _ q).mp h)).1 1
  exact fields_differ hv.symm

/-- Full E-equivalent values remain allowed. The first handle uses an actual
projection equation; literal equality of environments is not required. -/
theorem equivalent_old_values_allowed :
    extTarget.Realizes
      (Fin.cases (.unary .fst (.binary .pair payload (.name 123))) (fun _ => wrongFourth)) continuation := by
  apply (old_handle_target_has_complete_class _ _).mpr
  apply (Extended.frameProcess_realizes_iff _ _ _ _).mpr
  refine ⟨?_,.refl _⟩
  intro i
  fin_cases i
  · exact .equation (.fst _ _)
  · exact .refl _

noncomputable abbrev raw : Named (Fin 2) := .par canonical (.embed (.plain .nil))
noncomputable abbrev rawTarget : Named (Fin 2) := .par target (.embed (.plain .nil))

/-- The action and invariant also cover actual noncanonical parallel endpoints. -/
theorem padded_raw_output : Named.FreeStep raw (.output 8 0) rawTarget :=
  .parLeft _ actual_old_handle_output

theorem padded_raw_target_joint : Named.JointOpening rawTarget target := by
  have hj : Named.JointOpening raw canonical :=
    (Named.restrictedState_jointOpening (⟨φ,outputCode⟩ : ScopedState {40} 2)).structural_left
      (Named.Structural.zero canonical).symm
  exact hj.handle_output_target padded_raw_output (fun m q _ h => (full_output_is_deterministic m q h).2)

theorem target_private_channel_stays_blocked (b : Named (Fin 2)) (r : Recipe 2) :
    ¬ Named.FreeStep rawTarget (.input 7 r) b := by
  intro h
  exact padded_raw_target_joint.free_channel_public (⟨φ,continuation⟩ : ScopedState {40} 2) h (by change (7 : Nat) ∈ {7}; decide)

end ExplainableCrypto.Helios.Symbolic.SourceHandleOutputSPOT
