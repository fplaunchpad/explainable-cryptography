import ExplainableCrypto.Helios.Symbolic.SourceAdmissiblePrenex
import ExplainableCrypto.Helios.Symbolic.SourceFrameProjectionSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNamedAdmissibilitySPOT
open Historical General Source Extended

/-- Private name scopes do not turn two definitions of one public variable
into distinct variable definitions. -/
theorem duplicate_across_name_scopes_rejected :
    ¬ (Named.par (.newName (.base 40) (.embed (.active (0 : Fin 1) (.name 40))))
      (.newName (.base 41) (.embed (.active 0 (.name 41))))).UniqueDefinitions := by
  intro h
  exact h.2.2 0 ⟨rfl,rfl⟩

theorem equal_payload_distinct_handles_valid :
    (Named.newName (.base 40) (.embed (activeFrame
      (⟨fun _ : Fin 2 => (.name 40 : Ground)⟩ : Frame ∅ 2)))).WellFormed :=
  ⟨(activeFrame_wellFormed _).1,(activeFrame_wellFormed _).2⟩

abbrev orphan : Named Empty := .newVar (.embed (.plain (.output 0 (.var none) .nil)))

/-- A raw Open-Atom action can lack a definition. This pins why new_export
requires source uniqueness, rather than silently filtering the source rules. -/
theorem missing_definition_output_boundary :
    Named.BoundOutput orphan 0 (.embed (.plain .nil)) ∧
    ¬ orphan.UniqueDefinitions ∧ ¬ (Named.embed (.plain .nil) : Named (Option Empty)).Exports none :=
  ⟨.openAtom (.embed (.output 0 none .nil)),fun h => h.2,fun h => h⟩

theorem ordinary_input_needs_no_active_alias :
    (Named.newName (.base 40) (.embed (.plain (.input 4
      (.output 0 (.var none) .nil)))) : Named Empty).WellFormed :=
  ⟨True.intro,Named.closed_empty _⟩

abbrev oneHandle : Named (Fin 2) := .newName (.base 40) (.embed (.active 0 (.name 40)))
abbrev undefinedFourth : FreeLabel (Fin 2) :=
  .input 0 (.spk (.var 0) (.name 41) (.const .zero) (.var 1))

theorem undefined_fourth_label_field_rejected : ¬ oneHandle.LabelScoped undefinedFourth := by
  intro h
  have he : (1 : Fin 2) = 0 := h.2.2.2
  exact (by decide : (1 : Fin 2) ≠ 0) he

theorem defined_fourth_label_field_valid :
    (Named.embed (activeFrame (⟨fun _ : Fin 2 => (.name 40 : Ground)⟩ : Frame ∅ 2))).LabelScoped undefinedFourth :=
  Named.labelScoped_of_all_exports _ _ (activeFrame_exports _)

/-- The known raw Rewrite boundary remains visible in Named syntax. Unique
definitions survive, but arbitrary Closed representatives need not. -/
theorem named_raw_rewrite_closedness_boundary :
    (Named.newName (.base 40) (.embed SourceWellFormedSPOT.closedAlias)).WellFormed ∧
    Named.Structural (.newName (.base 40) (.embed SourceWellFormedSPOT.closedAlias))
      (.newName (.base 40) (.embed SourceWellFormedSPOT.openAlias)) ∧
    ¬ (Named.newName (.base 40) (.embed SourceWellFormedSPOT.openAlias)).Closed :=
  ⟨SourceWellFormedSPOT.raw_rewrite_closedness_counterexample.1,
    .newName _ (.embed SourceWellFormedSPOT.raw_rewrite_closedness_counterexample.2.1),
    SourceWellFormedSPOT.raw_rewrite_closedness_counterexample.2.2⟩

theorem alpha_keeps_export_and_uniqueness :
    ((Named.newName (.base 40) (.embed SourceNameInterpretationSPOT.binding)).Exports 0 ↔
      (Named.newName (.base 50) (.embed (SourceNameInterpretationSPOT.binding.mapNames
        SourceNameInterpretationSPOT.e id))).Exports 0) ∧
    ((Named.newName (.base 40) (.embed SourceNameInterpretationSPOT.binding)).UniqueDefinitions ↔
      (Named.newName (.base 50) (.embed (SourceNameInterpretationSPOT.binding.mapNames
        SourceNameInterpretationSPOT.e id))).UniqueDefinitions) :=
  ⟨SourceNameInterpretationSPOT.alpha_binding_representative.exports 0,
    SourceNameInterpretationSPOT.alpha_binding_representative.uniqueDefinitions⟩

abbrev beforeState : ScopedState {40} 1 :=
  ⟨SourceAtomicOutputSPOT.oldFrame,.output 0 SourceVisibleInterpretationSPOT.proofPayload .nil⟩
noncomputable def before : Named (Fin 1) := Named.restrictedState ∅ beforeState
noncomputable def after : Named (Option (Fin 1)) := Named.restrictedCapture ∅
  SourceAtomicOutputSPOT.oldFrame SourceVisibleInterpretationSPOT.proofPayload .nil

private theorem publication : Named.BoundOutput before 0 after := by
  exact (Named.BoundOutput.embed (frame_output_derivable _ _ _ _)).restrictNames _
    ((Named.output_restriction_fresh_iff 0).mpr (by simp))

theorem actual_restricted_state_valid : before.WellFormed := Named.restrictedState_wellFormed _ _

theorem actual_full_capture_target_valid : after.WellFormed :=
  Named.restrictedState_bound_target ∅ beforeState publication

theorem actual_output_defines_fresh_and_retains_old :
    after.Exports none ∧ after.Exports (some 0) ∧ (none : Option (Fin 1)) ≠ some 0 :=
  ⟨publication.new_export actual_restricted_state_valid.1,
    (publication.old_exports 0).mpr (Named.restrictedState_all_exports ∅ beforeState 0),by decide⟩

theorem actual_old_label_scope_shifts :
    after.LabelScoped ((FreeLabel.input 0 (.spk (.var 0) (.name 41) (.const .zero) (.var 0))).rename some) ↔
      before.LabelScoped (.input 0 (.spk (.var 0) (.name 41) (.const .zero) (.var 0))) :=
  publication.shifted_labelScoped _

theorem future_full_recipe_can_use_fresh_handle :
    after.LabelScoped (.input 0 (.spk (.var (some 0)) (.name 41) (.const .zero) (.var none))) :=
  Named.restrictedState_bound_target_labelScoped ∅ beforeState publication _

theorem actual_bound_factor_has_complete_variable_domains :
    ∃ (ns : List SourceName) (a : Extended (Fin 1)) (b : Extended (Option (Fin 1))),
      Named.Structural before (Named.restrictNames ns (.embed a)) ∧
      Named.Structural after (Named.restrictNames ns (.embed b)) ∧ Extended.BoundOutput a 0 b ∧
      (∀ n ∈ ns, n ≠ SourceName.channel 0) ∧ a.WellFormed ∧ b.WellFormed ∧
      (∀ v, a.Exports v) ∧ (∀ v, b.Exports v) :=
  publication.prenex_wellFormed actual_restricted_state_valid.1 (Named.restrictedState_all_exports ∅ beforeState)

theorem private_internal_factor_has_complete_variable_domains :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural SourceOperationalPrenexSPOT.beforeNamed (Named.restrictNames ns (.embed a)) ∧
      Named.Structural SourceOperationalPrenexSPOT.afterNamed (Named.restrictNames ns (.embed b)) ∧
      Extended.Reduction a b ∧ a.WellFormed ∧ b.WellFormed ∧
      (∀ v, a.Exports v) ∧ (∀ v, b.Exports v) :=
  SourceOperationalPrenexSPOT.private_internal_reconstructed.prenex_wellFormed
    (frameProcess_wellFormed _ _).1 (frameProcess_all_exports _ _)

theorem alpha_input_factor_has_complete_variable_domains :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural SourceOperationalPrenexSPOT.alphaSource (Named.restrictNames ns (.embed a)) ∧
      Named.Structural SourceOperationalPrenexSPOT.alphaTarget (Named.restrictNames ns (.embed b)) ∧
      Extended.FreeStep a (.input 0 (.name 40)) b ∧
      (∀ n ∈ ns, n ∉ (FreeLabel.input 0 (.name 40) : FreeLabel (Fin 1)).nameSupport) ∧
      a.WellFormed ∧ b.WellFormed ∧ (∀ v, a.Exports v) ∧ (∀ v, b.Exports v) ∧
      (FreeLabel.input 0 (.name 40)).VarsIn a.Exports := by
  apply SourceOperationalPrenexSPOT.alpha_input_reconstructed.prenex_wellFormed
  · exact ⟨True.intro,True.intro,fun _ h => h.2⟩
  · intro v
    exact Or.inl (Subsingleton.elim v 0)

end ExplainableCrypto.Helios.Symbolic.SourceNamedAdmissibilitySPOT
