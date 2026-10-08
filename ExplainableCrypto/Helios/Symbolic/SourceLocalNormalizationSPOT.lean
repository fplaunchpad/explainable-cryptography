import ExplainableCrypto.Helios.Symbolic.SourceNamedLocalNormalization
import ExplainableCrypto.Helios.Symbolic.SourceNamedFramePresentation

namespace ExplainableCrypto.Helios.Symbolic.SourceLocalNormalizationSPOT
open Historical General Source Extended

/-- The inner local depends on the outer local, and a public active handle
depends on the inner one. The expected final public value is literal 40. -/
abbrev innerContext : Extended (Option (Fin 1)) :=
  .newVar (.par (.active none (.var (some none))) (.active (some (some 0)) (.var none)))
abbrev intermediate : Extended (Fin 1) :=
  .newVar (.par (.active none (.name 40)) (.active (some 0) (.var none)))
abbrev nestedLocals : Extended (Fin 1) :=
  .newVar (.par (.active none (.name 40)) innerContext)

theorem outer_instantiation_exact : Instantiates (inputSubst (.name 40)) innerContext intermediate :=
  .newVar (.par (.active _ _ _ _ rfl) (.active _ _ _ _ rfl))

theorem dependent_local_chain_normalizes : Structural nestedLocals (.active 0 (.name 40)) := by
  have h := Structural.let_normalize (.name 40) (a := innerContext)
    (by simp [Exports]) outer_instantiation_exact
  exact h.trans (Structural.let_normalize (.name 40) (a := .active (some 0) (.var none))
    (by simp [Exports]) (.active _ _ _ _ rfl))

theorem dependent_chain_has_exact_domain : ∀ v : Fin 1, nestedLocals.Exports v := by
  intro v
  fin_cases v
  exact (dependent_local_chain_normalizes.exports _).mpr rfl

theorem dependent_chain_wellFormed : nestedLocals.WellFormed := by
  refine ⟨dependent_local_chain_normalizes.uniqueDefinitions.mpr True.intro,
    closed_of_all_exports _ dependent_chain_has_exact_domain⟩

/-- A wrong final public value is excluded by the full structural relation,
not only by the syntactic instantiation graph. -/
theorem wrong_chain_value_rejected : ¬ Structural nestedLocals (.active 0 (.name 41)) := by
  intro h
  have hr : (Extended.active (0 : Fin 1) (.name 40)).Realizes (fun _ => .name 40) .nil :=
    ⟨.refl _,.refl _⟩
  have hn := (dependent_local_chain_normalizes.realizes _ .nil).mpr hr
  have hw := (h.realizes _ .nil).mp hn
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp hw.1)

def literalFrame : Frame ∅ 1 := ⟨fun _ => .name 40⟩

theorem dependent_chain_has_complete_presentation :
    (Named.embed nestedLocals).RepresentsFrame ∅ literalFrame := by
  have h : Structural nestedLocals (activeFrame literalFrame) :=
    dependent_local_chain_normalizes.trans (Structural.zero (.active 0 (.name 40))).symm
  have hf := (Named.Structural.embed h).frameOf
  simpa only [Named.RepresentsFrame,Named.canonicalFrame,Named.restrictionNames,
    Finset.toList_empty,List.map,List.nil_append,Named.restrictNames,List.foldr,
    Named.frameOf,activeFrame_frameOf] using hf

/-- The target type is Empty. Input None remains its own binder; the old local
becomes the independently calculated literal pair in the second component. -/
abbrev inputContext : Extended (Option Empty) := .par
  (.plain (.output 0 (.var none) .nil))
  (.plain (.input 9 (.output 0 (.binary .pair (.var none) (.var (some none))) .nil)))
abbrev inputResult : Extended Empty := .par
  (.plain (.output 0 (.binary .pair (.name 40) (.const .one)) .nil))
  (.plain (.input 9 (.output 0 (.binary .pair (.var none)
    (.binary .pair (.name 40) (.const .one))) .nil)))

theorem empty_target_instantiation :
    Instantiates (inputSubst (.binary .pair (.name 40) (.const .one))) inputContext inputResult :=
  .par (.plain _ _) (.plain _ _)

theorem input_binder_survives_local_elimination :
    Structural (.newVar (.par (.active none (.binary .pair (.name 40) (.const .one))) inputContext)) inputResult :=
  Structural.let_normalize _ (by simp [Exports]) empty_target_instantiation

theorem captured_input_result_rejected :
    ¬ Instantiates (inputSubst (.binary .pair (.name 40) (.const .one))) inputContext
      (.par (.plain (.output 0 (.binary .pair (.name 40) (.const .one)) .nil))
        (.plain (.input 9 (.output 0 (.binary .pair (.var none) (.var none)) .nil)))) := by
  intro h
  have he := empty_target_instantiation.unique h
  cases he

/-- Full substitution traverses the proof's fourth field as well as its key. -/
theorem full_proof_local_elimination :
    Structural
      (.newVar (.par (.active none (.name 40))
        (.active (some (0 : Fin 1)) (.spk (.var none) (.name 42) (.const .zero)
          (.ternary .penc (.var none) (.name 42) (.const .one))))))
      (.active 0 (.spk (.name 40) (.name 42) (.const .zero)
        (.ternary .penc (.name 40) (.name 42) (.const .one)))) :=
  by
    apply Structural.let_normalize (.name 40)
    · simp [Exports]
    · exact .active _ _ _ _ rfl

/-- A context that redefines the local violates the necessary side condition;
even equal payloads do not license erasing duplicate definitions. -/
theorem duplicate_local_cannot_be_erased :
    ¬ Structural (Extended.newVar (.par (.active none (.name 40 : Term (Option Empty)))
      (.active none (.name 40)))) (.plain .nil) := by
  intro h
  have hu := h.uniqueDefinitions.mpr True.intro
  exact hu.1.2.2 none ⟨rfl,rfl⟩

theorem active_domain_cannot_be_instantiated_by_name :
    ¬ ∃ b : Extended Empty, Instantiates (inputSubst (.name 40)) (.active none (.const .zero)) b := by
  rintro ⟨b,h⟩
  cases h with
  | active _ _ y _ _ => exact y.elim

abbrev privateBody : Named (Option (Fin 1)) :=
  .embed (.active (some 0) (.binary .pair (.name 40) (.var none)))
abbrev privateLocal : Named (Fin 1) := .newVar
  (.par (.embed (.active none (.name 40))) (.newName (.base 40) privateBody))

/-- The external provider literal stays 40 while the context's private 40
becomes 41. This pins an actual final representative, not only an existential. -/
theorem private_name_local_normalizes_without_capture :
    Named.Structural privateLocal (.newName (.base 41)
      (.embed (.active 0 (.binary .pair (.name 41) (.name 40))))) := by
  let provider : Named (Option (Fin 1)) := .embed (.active none (.name 40))
  let body : Named (Option (Fin 1)) := .embed (.active (some 0) (.binary .pair (.name 41) (.var none)))
  have halpha : Named.Structural (.newName (.base 40) privateBody) (.newName (.base 41) body) := by
    simpa [privateBody,body,Named.mapNames,Extended.mapNames,Term.mapNames] using
      Named.Structural.alphaBase privateBody 40 41 (by decide)
  have he : Named.Structural (.newVar (.par provider body))
      (.embed (.active 0 (.binary .pair (.name 41) (.name 40)))) := by
    apply (Named.Structural.newVar (Named.Structural.embedPar _ _).symm).trans
    apply (Named.Structural.embedVar _).symm.trans
    apply Named.Structural.embed
    apply Structural.let_normalize (.name 40)
    · simp [Exports]
    · exact .active _ _ _ _ rfl
  exact (Named.Structural.newVar (Named.Structural.parRight provider halpha)).trans
    ((Named.Structural.newVar (Named.Structural.namePar provider (.base 41) body (by decide))).trans
      ((Named.Structural.nameVarComm (.base 41) (.par provider body)).symm.trans
        (Named.Structural.newName (.base 41) he)))

theorem fresh_named_normalization_exists :
    ∃ (ns : List SourceName) (b : Extended (Option (Fin 1))) (c : Extended (Fin 1)),
      Named.Structural (.newName (.base 40) privateBody) (Named.restrictNames ns (.embed b)) ∧
      (∀ n ∈ ns, n ∉ (Extended.active none (shiftTerm (.name 40 : Term (Fin 1)))).nameSupport) ∧
      ¬ b.Exports none ∧ Instantiates (inputSubst (.name 40)) b c ∧
      Named.Structural privateLocal (Named.restrictNames ns (.embed c)) :=
  Named.let_normalize_fresh (.name 40) (.newName (.base 40) privateBody) (by simp [Named.Exports,Exports])

/-- The two literals have different full-E observations after freshening;
naive capture would make this equality true. -/
theorem private_and_external_literals_remain_distinct :
    ¬ EqE (.name 41 : Ground) (.name 40) := by
  intro h
  exact (by decide : (41 : Nat) ≠ 40) ((EqE.name_iff 41 40).mp h)

end ExplainableCrypto.Helios.Symbolic.SourceLocalNormalizationSPOT
