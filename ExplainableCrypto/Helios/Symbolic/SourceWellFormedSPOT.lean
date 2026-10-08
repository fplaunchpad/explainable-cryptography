import ExplainableCrypto.Helios.Symbolic.SourceWellFormedPreservation
import ExplainableCrypto.Helios.Symbolic.SourceFrameInputSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceWellFormedSPOT
open Historical General Source Extended

/-- Two copies of even the same payload cannot define one variable twice. -/
theorem duplicate_definition_rejected :
    ¬ (Extended.par (.active (0 : Fin 1) (.name 40)) (.active 0 (.name 40))).UniqueDefinitions := by
  intro h
  exact h.2.2 0 ⟨rfl,rfl⟩

/-- Variable restriction requires an active definition; closed-looking null
syntax does not discharge the source's exactly-one-definition condition. -/
theorem missing_local_definition_rejected :
    ¬ (Extended.newVar (.plain .nil) : Extended Empty).WellFormed := by
  intro h
  exact h.1.2

/-- An input binder is bound by the prefix and correctly needs no active alias. -/
theorem ordinary_input_binder_valid :
    (Extended.plain (.input 4 (.output 0 (.var none) .nil)) : Extended Empty).WellFormed :=
  ⟨True.intro,closed_empty _⟩

/-- Ground lets bind their one alias, even when its continuation has another
input whose variable appears separately in the emitted pair. -/
theorem nested_ground_let_valid :
    (letTerm (.name 40 : Ground) (.input 4
      (.output 0 (.binary .pair (.var (some none)) (.var none)) .nil))).WellFormed :=
  ground_let_wellFormed _ _

/-- Equal values under distinct public variable names remain valid. -/
theorem equal_payload_distinct_definitions_valid :
    (activeFrame (⟨fun _ : Fin 2 => (.name 40 : Ground)⟩ : Frame ∅ 2)).WellFormed :=
  activeFrame_wellFormed _

/-- Closedness checks the fourth proof field, even though this field is opaque
to most observers and the active variable itself has a definition. -/
theorem undefined_proof_field_rejected :
    ¬ (Extended.active (0 : Fin 2) (.spk (.name 40) (.name 41) (.const .zero) (.var 1))).Closed := by
  intro h
  have he : (1 : Fin 2)=0 := h.2.2.2.2
  exact (by decide : (1 : Fin 2) ≠ 0) he

def closedAlias : Extended (Fin 2) := .active 0 (.name 40)
def openAlias : Extended (Fin 2) := .active 0 (.unary .fst (.binary .pair (.name 40) (.var 1)))

/-- The raw rewrite relation can insert an undefined variable into a discarded
projection argument. This refutes unrestricted closedness preservation, not
privacy, and is retained as a guard against an overstrong source claim. -/
theorem raw_rewrite_closedness_counterexample :
    closedAlias.WellFormed ∧ Structural closedAlias openAlias ∧ ¬ openAlias.Closed := by
  refine ⟨⟨True.intro,⟨rfl,True.intro⟩⟩,?_,?_⟩
  · exact .rewrite 0 (EqE.equation (.fst (.name 40) (.var 1))).symm
  · intro h
    have he : (1 : Fin 2)=0 := h.2.2
    exact (by decide : (1 : Fin 2) ≠ 0) he

/-- The counterexample lacks the stronger actual-frame property: its unused
ambient variable 1 is not exported. -/
theorem counterexample_domain_not_covered : ¬ (∀ v, closedAlias.Exports v) := by
  intro h
  exact (by decide : (1 : Fin 2) ≠ 0) (h 1)

/-- When both variables really are defined, the same raw rewrite stays
well-formed. Its previously discarded variable now has an actual binding. -/
theorem covered_rewrite_stays_valid :
    (Extended.par openAlias (.active 1 (.name 41))).WellFormed := by
  have hu : (Extended.par closedAlias (.active 1 (.name 41))).UniqueDefinitions := by
    refine ⟨True.intro,True.intro,?_⟩
    intro v ⟨h₀,h₁⟩
    exact (by decide : (0 : Fin 2) ≠ 1) (h₀.symm.trans h₁)
  have he : ∀ v, (Extended.par closedAlias (.active 1 (.name 41))).Exports v := by
    intro v
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact (Structural.parLeft _ raw_rewrite_closedness_counterexample.2.1).wellFormed_of_all_exports hu he

/-- The actual fresh-output target is well-formed before fresh-to-last-handle
renaming, so the new variable has one definition and every old one survives. -/
theorem actual_capture_valid :
    (Extended.par ((activeFrame SourceAtomicOutputSPOT.oldFrame).rename some)
      (capture (groundTerm (.name 40)) (groundAgent Agent.nil))).WellFormed :=
  frame_capture_wellFormed _ _ _

/-- Every actual historical stage has a closed, uniquely defined variable/frame
representation, including pending and rejected stages. -/
theorem election_stage_valid (swap : Bool) (phase : Process.Phase) :
    (frameProcess (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right phase)
      (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical phase)).WellFormed :=
  frameProcess_wellFormed _ _
end ExplainableCrypto.Helios.Symbolic.SourceWellFormedSPOT
