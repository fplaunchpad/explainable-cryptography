import ExplainableCrypto.Helios.Symbolic.SourceExtendedSubstitution
import ExplainableCrypto.Helios.Symbolic.SourceNamedGeneralSubstitution

namespace ExplainableCrypto.Helios.Symbolic.SourceExtendedSubstitutionSPOT
open Historical General Source Extended

abbrev dependent : Extended (Fin 2) := .par (.active 1 (.const .zero)) (.active 0 (.var 1))
abbrev normalized : Extended (Fin 2) := .par (.active 1 (.const .zero)) (.active 0 (.const .zero))
def zeros : Frame ∅ 2 := ⟨fun _ => .const .zero⟩

/-- The provider remains active while its value propagates into the other
active definition. This is an actual source structural path. -/
theorem dependent_alias_normalizes : Structural dependent normalized := by
  simpa [substFree,replaceVar,Term.subst] using
    Structural.substExtended (1 : Fin 2) (.const .zero) (.active 0 (.var 1)) (by change (1 : Fin 2) ≠ 0; decide)

theorem dependent_alias_wellFormed : dependent.WellFormed := by
  refine ⟨⟨True.intro,True.intro,?_⟩,closed_of_all_exports _ ?_⟩
  · intro v ⟨h1,h0⟩
    exact (by decide : (1 : Fin 2) ≠ 0) (h1.symm.trans h0)
  · intro v
    fin_cases v
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem normalized_alias_stays_wellFormed : normalized.WellFormed :=
  dependent_alias_normalizes.wellFormed_of_all_exports dependent_alias_wellFormed.1 (by
    intro v
    fin_cases v
    · exact Or.inr rfl
    · exact Or.inl rfl)

private theorem dependent_realizes : dependent.Realizes (fun _ => .const .zero) .nil :=
  ⟨.nil,.nil,⟨.refl _,.refl _⟩,⟨.refl _,.refl _⟩,.of_parEq (.zero _)⟩

theorem wrong_active_value_cannot_normalize :
    ¬ Structural dependent (.par (.active 1 (.const .zero)) (.active 0 (.const .one))) := by
  intro h
  obtain ⟨_,_,_,hq,_⟩ := (h.realizes (fun _ => .const .zero) .nil).mp dependent_realizes
  exact zero_not_one hq.1

/-- Without the provider's constraint, changing the dependent active payload
is invalid even through arbitrary structural paths of the expanded model. -/
theorem provider_constraint_cannot_be_omitted :
    ¬ Structural (.active (0 : Fin 2) (.var 1)) (.active 0 (.const .zero)) := by
  intro h
  have hq := (h.realizes (fun _ => .const .one) .nil).mp ⟨EqE.refl _,Agent.EvalEq.refl _⟩
  exact zero_not_one hq.1.symm

theorem duplicate_provider_rejected :
    ¬ (Extended.par (.active (1 : Fin 2) (.const .zero)) (.active 1 (.var 0))).UniqueDefinitions := by
  intro h
  exact h.2.2 1 ⟨rfl,rfl⟩

abbrev scopedContext : Extended Nat := .newVar (.par (.active none (.var (some 0)))
  (.plain (.input 9 (.output 0 (.binary .pair (.var none)
    (.binary .pair (.var (some none)) (.var (some (some 0))))) .nil))))

/-- Both the restricted None and the input's newer None are kept distinct
from the shifted outer substitution variable and its full replacement. -/
theorem nested_binders_substitute_outer_variable : scopedContext.substFree 0 (.var 1) =
    .newVar (.par (.active none (.var (some 1)))
      (.plain (.input 9 (.output 0 (.binary .pair (.var none)
        (.binary .pair (.var (some none)) (.var (some (some 1))))) .nil)))) := by
  simp [substFree,replaceVar,shiftTerm,Term.subst,Agent.subst,liftSubst]

theorem shifted_replacement_does_not_capture_local :
    (Extended.newVar (.active none (.var (some (0 : Nat))))).substFree 0 (.var 1) ≠
      .newVar (.active none (.var none)) := by
  simp [substFree,replaceVar,shiftTerm,Term.subst]

theorem nested_context_substitution_derivable :
    Structural (.par (.active 0 (.var 1)) scopedContext) (.par (.active 0 (.var 1)) (scopedContext.substFree 0 (.var 1))) :=
  Structural.substExtended 0 (.var 1) scopedContext (by simp [Exports])

theorem full_proof_field_substitution_derivable :
    Structural
      (.par (.active (1 : Fin 2) (.name 40)) (.active 0 (.spk (.var 1) (.name 41) (.const .zero)
        (.ternary .penc (.var 1) (.var 1) (.const .one)))))
      (.par (.active (1 : Fin 2) (.name 40)) (.active 0 (.spk (.name 40) (.name 41) (.const .zero)
        (.ternary .penc (.name 40) (.name 40) (.const .one))))) := by
  simpa [substFree,replaceVar,Term.subst] using Structural.substExtended (1 : Fin 2) (.name 40)
    (.active 0 (.spk (.var 1) (.name 41) (.const .zero) (.ternary .penc (.var 1) (.var 1) (.const .one)))) (by change (1 : Fin 2) ≠ 0; decide)

/-- The newly normalized dependent frame has a concrete complete ground
presentation, including both original handles. -/
theorem dependent_frame_has_complete_presentation :
    (Named.embed dependent).RepresentsFrame ∅ zeros := by
  have hz : Structural normalized (activeFrame zeros) := by
    exact Structural.parRight (.active (1 : Fin 2) (.const .zero))
      (Structural.zero (.active (0 : Fin 2) (.const .zero))).symm
  have hs := Named.Structural.embed (dependent_alias_normalizes.trans hz)
  simpa only [Named.RepresentsFrame,Named.canonicalFrame,Named.restrictionNames,
    Finset.toList_empty,List.map,List.nil_append,Named.restrictNames,List.foldr,
    Named.frameOf,Extended.frameOf] using hs

theorem dependent_frame_static_witness : Named.StaticEq (.embed dependent) (Named.canonicalFrame ∅ zeros) :=
  .of_presentations dependent_frame_has_complete_presentation (Named.canonicalFrame_represents zeros) (.refl zeros)

abbrev privateContext : Named (Fin 2) := .newName (.base 40)
  (.embed (.active 0 (.binary .pair (.name 40) (.var 1))))

/-- The provider's external literal 40 must not become bound by the context's
old private-name binder. The derived rule chooses a fresh actual representative. -/
theorem named_substitution_avoids_provider_capture :
    ∃ (ns : List SourceName) (b : Extended (Fin 2)),
      Named.Structural privateContext (Named.restrictNames ns (.embed b)) ∧ ¬ b.Exports 1 ∧
      (∀ n ∈ ns, n ∉ (Extended.active (1 : Fin 2) (.name 40)).nameSupport) ∧
      Named.Structural (.par (.embed (.active 1 (.name 40))) privateContext)
        (.par (.embed (.active 1 (.name 40))) (Named.restrictNames ns (.embed (b.substFree 1 (.name 40))))) :=
  Named.Structural.substNamed_fresh 1 (.name 40) privateContext (by change (1 : Fin 2) ≠ 0; decide)

/-- Capturing an external literal would equate two names that remain distinct
after the bound name is freshened; full E does not identify those names. -/
theorem captured_literal_equality_rejected :
    EqE (.name 40 : Ground) (.name 40) ∧ ¬ EqE (.name 50 : Ground) (.name 40) := by
  refine ⟨.refl _,?_⟩
  intro h
  exact (by decide : (50 : Nat) ≠ 40) ((EqE.name_iff 50 40).mp h)

end ExplainableCrypto.Helios.Symbolic.SourceExtendedSubstitutionSPOT
