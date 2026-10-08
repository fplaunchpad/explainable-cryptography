import ExplainableCrypto.Helios.Symbolic.OuterFusion

namespace ExplainableCrypto.Helios.Symbolic.OuterFusionSPOT

abbrev a : Term Nat := .ternary .penc (.name 0) (.name 1) (.const .zero)
abbrev b : Term Nat := .ternary .penc (.name 0) (.name 2) (.const .one)
abbrev aa : Term Nat := combinedCiphertext (.name 0) (.name 1) (.name 1) (.const .zero) (.const .zero)
abbrev ab : Term Nat := combinedCiphertext (.name 0) (.name 1) (.name 2) (.const .zero) (.const .one)
abbrev repeatedSource : Term Nat := .binary .mul (.binary .mul a a) b
abbrev repeatedLeft : Term Nat := .binary .mul aa b
abbrev repeatedRight : Term Nat := .binary .mul ab a

theorem repeated_left_fusion : OuterFusion repeatedSource repeatedLeft := by
  apply OuterFusion.of_factors _ _ (.name 0) (.name 1) (.name 1) (.const .zero) (.const .zero) {b.baseClass}
  · simp [Term.mulFactors, ciphertextPairFactors, a]
  · simp [Term.mulFactors]

theorem repeated_right_fusion : OuterFusion repeatedSource repeatedRight := by
  apply OuterFusion.of_factors _ _ (.name 0) (.name 1) (.name 2) (.const .zero) (.const .one) {a.baseClass}
  · have he : BaseEq repeatedSource (.binary .mul (.binary .mul a b) a) :=
      (BaseEq.equation (.assoc .mul trivial a a b)).trans
        ((BaseEq.binary .mul (.refl _) (.equation (.comm .mul trivial a b))).trans
          (BaseEq.equation (.assoc .mul trivial a b a)).symm)
    simpa only [Term.mulFactors, ciphertextPairFactors, Multiset.singleton_add,
      Multiset.insert_eq_cons] using he.mul_factors
  · simp [Term.mulFactors]

/-- The exhaustive theorem covers a duplicated ciphertext shared by two selections. -/
theorem repeated_selection_peak : ModuloStep repeatedSource repeatedLeft ∧
    ModuloStep repeatedSource repeatedRight ∧ JoinModulo repeatedLeft repeatedRight ∧
      repeatedLeft ≠ repeatedRight := by
  have h := outer_fusion_peak_joined repeated_left_fusion repeated_right_fusion
  exact ⟨h.1, h.2.1, h.2.2, by decide⟩

abbrev oneKey : Term Nat := .const .one
abbrev sumKey : Term Nat := .binary .add (.const .zero) (.const .one)
abbrev keySource : Term Nat := .binary .mul
  (.ternary .penc oneKey (.name 1) (.const .zero))
  (.ternary .penc sumKey (.name 2) (.const .one))
abbrev keyLeft : Term Nat := combinedCiphertext oneKey (.name 1) (.name 2) (.const .zero) (.const .one)
abbrev keyRight : Term Nat := combinedCiphertext sumKey (.name 1) (.name 2) (.const .zero) (.const .one)

theorem background_key_fusion : OuterFusion keySource keyLeft := by
  apply OuterFusion.of_factors _ _ oneKey (.name 1) (.name 2) (.const .zero) (.const .one) 0
  · have hc : (Term.ternary .penc sumKey (.name 2) (.const .one)).baseClass =
        (Term.ternary .penc oneKey (.name 2) (.const .one)).baseClass :=
      (baseClass_eq_iff _ _).mpr (.ternary .penc (.equation .zero_one) (.refl _) (.refl _))
    simp [Term.mulFactors, ciphertextPairFactors, hc]
  · simp [keyLeft, Term.mulFactors]

theorem equivalent_key_outputs_base : BaseEq keyLeft keyRight :=
  .ternary .penc (BaseEq.equation .zero_one).symm (.refl _) (.refl _)

/-- Raw matching fails, but either E0-equivalent key representative gives a joined endpoint. -/
theorem background_key_peak : (rootReduce keySource).map Subtype.val = none ∧
    ModuloStep keySource keyLeft ∧ ModuloStep keySource keyRight ∧
      JoinModulo keyLeft keyRight ∧ keyLeft ≠ keyRight := by
  have hr : OuterFusion keySource keyRight := by
    unfold OuterFusion
    rw [← equivalent_key_outputs_base.mul_factors]
    exact background_key_fusion
  have h := outer_fusion_peak_joined background_key_fusion hr
  exact ⟨by decide, h.1, h.2.1, h.2.2, by decide⟩

/-- Outer fusion is a proper subrelation of modulo reduction. -/
theorem projection_is_not_outer_fusion :
    ModuloStep (Term.unary .fst (.binary .pair (.name 0) (.name 1)) : Term Nat) (.name 0) ∧
      ¬ OuterFusion (.unary .fst (.binary .pair (.name 0) (.name 1)) : Term Nat) (.name 0) := by
  refine ⟨(RootStep.fst (.name 0) (.name 1)).to_modulo, ?_⟩
  intro h
  have hc := h.card_step
  simp [Term.mulFactors] at hc

abbrev internalSource : Term Nat := .binary .mul
  (.ternary .penc (.unary .fst (.binary .pair (.name 0) (.const .bottom)))
    (.name 1) (.const .zero))
  (.ternary .penc (.name 0) (.name 2) (.const .one))
abbrev internalTarget : Term Nat := .binary .mul
  (.ternary .penc (.name 0) (.name 1) (.const .zero))
  (.ternary .penc (.name 0) (.name 2) (.const .one))

/-- An internal key reduction enables fusion while preserving the outer factor count. -/
theorem internal_key_enables_fusion :
    ModuloStep internalSource internalTarget ∧
      ¬ OuterFusion internalSource internalTarget ∧
      (rootReduce internalSource).isNone = true ∧
      (rootReduce internalTarget).isSome = true := by
  refine ⟨(RootStep.fst (.name 0) (.const .bottom)).to_modulo.context
    (.binaryLeft .mul (.ternaryFirst .penc .hole (.name 1) (.const .zero))
      (.ternary .penc (.name 0) (.name 2) (.const .one))), ?_, by decide, by decide⟩
  intro h
  have hc := h.card_step
  simp [Term.mulFactors] at hc

end ExplainableCrypto.Helios.Symbolic.OuterFusionSPOT
