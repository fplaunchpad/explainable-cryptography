import ExplainableCrypto.Helios.Symbolic.SourceReachableFramePrefix
import ExplainableCrypto.Helios.Symbolic.SourceReachableElectionSPOT
import ExplainableCrypto.Helios.Symbolic.SourcePresentationAlignmentSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceVariableFramePrefixSPOT
open Historical General Source Extended

abbrev old : Extended (Option (Fin 1)) := .active (some 0) (.name 99)
abbrev inner : Extended (Option (Option (Option (Fin 1)))) :=
  .par (.active none (.const .one))
    (.active (some (some none)) (.binary .pair (.var (some none)) (.var none)))
abbrev raw : Extended (Option (Fin 1)) :=
  .par old (.newVar (.par (.active none (.const .zero)) (.newVar inner)))
abbrev gathered : Extended (LocalVars 2 (Option (Fin 1))) :=
  .par (.par (.active (some (some (some 0))) (.name 99))
    (.active (some none) (.const .zero))) inner

/-- Independent coordinates: old public 0 crosses both locals, the fresh
public slot remains distinct, and the captured pair uses both local providers. -/
theorem two_local_capture_hoists_with_all_providers :
    Structural raw (closeVars 2 gathered) ∧ gathered.FrameForest ∧
      gathered.UniqueDefinitions ∧ (∀ v, gathered.Exports v) := by
  refine ⟨?_,by simp [FrameForest],
    by simp [UniqueDefinitions,Exports,LocalVars],
    by
      intro v
      cases v with
      | none => exact Or.inr (Or.inl rfl)
      | some v => cases v with
        | none => exact Or.inl (Or.inr rfl)
        | some v => cases v with
          | none => exact Or.inr (Or.inr rfl)
          | some v => exact Or.inl (Or.inl (by congr 3; exact Fin.eq_zero v))⟩
  exact (Structural.newPar old _).trans (.newVar
    ((Structural.assoc _ _ _).symm.trans (Structural.newPar _ inner)))

theorem public_coordinates_do_not_merge_with_locals :
    outerVar 2 (none : Option (Fin 1)) = some (some none) ∧
    outerVar 2 (some (0 : Fin 1)) = some (some (some 0)) ∧
    outerVar 2 (none : Option (Fin 1)) ≠ none ∧
    outerVar 2 (none : Option (Fin 1)) ≠ some none ∧
    outerVar 2 (none : Option (Fin 1)) ≠ outerVar 2 (some (0 : Fin 1)) := by
  dsimp [outerVar,LocalVars]
  decide

abbrev values : LocalVars 2 (Option (Fin 1)) → Ground
  | none => .const .one
  | some none => .const .zero
  | some (some none) => .binary .pair (.const .zero) (.const .one)
  | some (some (some _)) => .name 99

theorem gathered_capture_has_independent_expected_values : gathered.Satisfies values :=
  ⟨⟨.refl _,.refl _⟩,⟨.refl _,.refl _⟩⟩

theorem fresh_provider_can_be_extracted_without_dropping_others :
    ∃ (m : Term (LocalVars 2 (Option (Fin 1)))) (b : Extended (LocalVars 2 (Option (Fin 1)))),
      b.FrameForest ∧ ¬ b.Exports (some (some none)) ∧
      Structural gathered (.par (.active (some (some none)) m) b) :=
  two_local_capture_hoists_with_all_providers.2.1.extract_provider
    two_local_capture_hoists_with_all_providers.2.2.1 (Or.inr (Or.inr rfl))

/-- Hoisting leaves the cyclic constraint as an explicit provider; it does not
turn an inhabited semantic class into a ground presentation. -/
theorem cyclic_forest_is_retained_and_still_not_presentable :
    (Extended.active none (.var none) : Extended (LocalVars 1 (Fin 0))).FrameForest ∧
    (Extended.active none (.var none) : Extended (LocalVars 1 (Fin 0))).UniqueDefinitions ∧
    (∀ v, (Extended.active none (.var none) : Extended (LocalVars 1 (Fin 0))).Exports v) ∧
    ¬ Named.Structural (.embed (closeVars 1 (.active none (.var none)) : Extended (Fin 0)))
      (.embed (.plain .nil)) := by
  exact ⟨True.intro,True.intro,by dsimp [LocalVars,Exports]; decide,Named.unconstrained_local_not_structural⟩

/-- Actual fresh output supplies every extraction premise from its old frame.
The target's private name allocation is freshened against both literal sets. -/
theorem actual_private_output_extracts_complete_forest :
    ∃ (ns : List SourceName) (n : Nat) (d : Extended (LocalVars n (Option (Fin 0)))),
      d.FrameForest ∧ d.UniqueDefinitions ∧ (∀ v, d.Exports v) ∧
      (∀ x ∈ ns, x ∉ ({.base 40,.channel 0} : Finset SourceName) ∪
        SourceFrameCompatibilitySPOT.latentPrivateCapture.frameOf.allNames) ∧
      Named.Structural SourceFrameCompatibilitySPOT.latentPrivateCapture.frameOf
        (Named.restrictNames ns (.embed (closeVars n d))) :=
  SourceFrameCompatibilitySPOT.latent_private_name_has_actual_output.exists_complete_frame_prefix
    SourceFrameCompatibilitySPOT.latent_private_name_can_be_retained_in_old_policy _

/-- Real mixed historical execution includes two publications, adaptive input,
and replay rejection. Its complete forest is extracted from that execution. -/
theorem actual_rejected_execution_extracts_complete_forest (swap : Bool) :
    ∃ (phase : Process.Phase) (i : Fin 3 ≃ Fin phase.handles)
      (names : List SourceName) (n : Nat) (d : Extended (LocalVars n (Fin phase.handles))),
      Process.Reachable SourceReachableElectionSPOT.ns swap SourceReachableElectionSPOT.left
        SourceReachableElectionSPOT.right 1 phase ∧
      d.FrameForest ∧ d.UniqueDefinitions ∧ (∀ v, d.Exports v) ∧
      Named.Structural ((SourceReachableElectionSPOT.raw swap (.rejected [])).rename i).frameOf
        (Named.restrictNames names (.embed (closeVars n d))) := by
  have hl : NoncesFreshFor SourceReachableElectionSPOT.ns SourceReachableElectionSPOT.left.value := by
    unfold NoncesFreshFor
    decide
  have hr : NoncesFreshFor SourceReachableElectionSPOT.ns SourceReachableElectionSPOT.right.value := by
    unfold NoncesFreshFor
    decide
  obtain ⟨phase,_,_,i,hphase,_,names,n,d,hd,hu,hx,_,hs⟩ :=
    scopedVoterElection_execution_frame_prefix _ NumericReflectionSPOT.fixture_names_fresh swap
      _ _ hl hr 1 _ Channels.canonical_fresh
      (SourceReachableElectionSPOT.actual_mixed_execution_rejects swap) ∅
  exact ⟨phase,i,names,n,d,hphase,hd,hu,hx,hs⟩

end ExplainableCrypto.Helios.Symbolic.SourceVariableFramePrefixSPOT
