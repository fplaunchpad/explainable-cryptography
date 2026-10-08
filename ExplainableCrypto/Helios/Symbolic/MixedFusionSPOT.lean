import ExplainableCrypto.Helios.Symbolic.FactorStepCoverage
import ExplainableCrypto.Helios.Symbolic.RootReduction

namespace ExplainableCrypto.Helios.Symbolic.MixedFusionSPOT

abbrev oldKey : Term Nat := .unary .fst (.binary .pair (.name 0) (.const .bottom))
abbrev first : Term Nat := .ternary .penc oldKey (.name 1) (.const .zero)
abbrev second : Term Nat := .ternary .penc oldKey (.name 2) (.const .one)
abbrev changed : Term Nat := .ternary .penc (.name 0) (.name 1) (.const .zero)
abbrev merged : Term Nat := combinedCiphertext oldKey (.name 1) (.name 2) (.const .zero) (.const .one)
abbrev keySource : Term Nat := .binary .mul (.binary .mul first (.name 9)) second
abbrev keyFused : Term Nat := .binary .mul merged (.name 9)
abbrev keyChanged : Term Nat := .binary .mul (.binary .mul changed (.name 9)) second

theorem key_fusion : OuterFusion keySource keyFused := by
  apply OuterFusion.of_factors _ _ oldKey (.name 1) (.name 2) (.const .zero) (.const .one)
    {(Term.name 9 : Term Nat).baseClass}
  · simp only [Term.mulFactors, ciphertextPairFactors, Multiset.insert_eq_cons,
      Multiset.cons_add, Multiset.singleton_add]
    exact congrArg (fun xs => first.baseClass ::ₘ xs) (Multiset.pair_comm _ _)
  · rfl

theorem key_factor_step : FactorStep keySource keyChanged := by
  refine ⟨first, changed, {(Term.name 9 : Term Nat).baseClass, second.baseClass}, rfl,
    (RootStep.fst (.name 0) (.const .bottom)).to_modulo.context
      (.ternaryFirst .penc .hole (.name 1) (.const .zero)), ?_, ?_⟩ <;>
    simp only [Term.mulFactors, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]

/-- A nonadjacent selected ciphertext changes one key copy and retains the name. -/
theorem key_mixed_peak : ModuloStep keySource keyFused ∧ ModuloStep keySource keyChanged ∧
    JoinModulo keyFused keyChanged ∧ keyFused ≠ keyChanged :=
  ⟨(fusion_factor_peak_joined key_fusion key_factor_step).1,
    (fusion_factor_peak_joined key_fusion key_factor_step).2.1,
    outer_fusion_modulo_peak_joined key_fusion key_factor_step.to_modulo, by decide⟩

/-- The gate's minimized false key-copy claim, on the exposed pair itself. -/
theorem one_key_copy_blocks_fusion :
    (rootReduce (.binary .mul changed second)).isNone = true ∧
      (rootReduce (.binary .mul first second)).isSome = true := by decide

abbrev finalKey : Term Nat := .binary .mul
  (combinedCiphertext (.name 0) (.name 1) (.name 2) (.const .zero) (.const .one)) (.name 9)

/-- Independent fixed endpoint: both routes reach the specified updated ciphertext. -/
theorem key_routes_expected : ReducesModulo keyFused finalKey ∧ ReducesModulo keyChanged finalKey := by
  have hk := (RootStep.fst (V := Nat) (.name 0) (.const .bottom)).to_modulo
  refine ⟨.single (hk.context (.binaryLeft .mul
    (.ternaryFirst .penc .hole (.binary .compose (.name 1) (.name 2))
      (.binary .add (.const .zero) (.const .one))) (.name 9))), ?_⟩
  let updated : Term Nat := .binary .mul (.binary .mul changed (.name 9))
    (.ternary .penc (.name 0) (.name 2) (.const .one))
  have hstep : ModuloStep keyChanged updated := hk.context
    (.binaryRight .mul (.binary .mul changed (.name 9))
      (.ternaryFirst .penc .hole (.name 2) (.const .one)))
  refine .head hstep (.single ?_)
  apply homomorphic_step_of_factors
  simp only [updated, Term.mulFactors, Multiset.insert_eq_cons,
    Multiset.cons_add, Multiset.singleton_add]
  exact congrArg (fun xs => changed.baseClass ::ₘ xs) (Multiset.pair_comm _ _)

/-- An E0 change in an unchanged argument is absorbed by ciphertext-step inversion. -/
theorem background_target_join :
    let a : Term Nat := .ternary .penc oldKey (.const .one) (.const .zero)
    let b : Term Nat := .ternary .penc (.name 0) (.binary .add (.const .zero) (.const .one)) (.const .zero)
    ModuloStep a b ∧ JoinModulo
      (combinedCiphertext oldKey (.const .one) (.name 2) (.const .zero) (.const .one))
      (.binary .mul b second) := by
  have h : ModuloStep (.ternary .penc oldKey (.const .one) (.const .zero))
      (.ternary .penc (.name 0) (.binary .add (.const .zero) (.const .one)) (.const .zero)) :=
    ((RootStep.fst (.name 0) (.const .bottom)).to_modulo.context
      (.ternaryFirst .penc .hole (.const .one) (.const .zero))).post_base
        (.ternary .penc (.refl _) (BaseEq.equation .zero_one).symm (.refl _))
  exact ⟨h, fusion_ciphertext_peak_joined oldKey (.const .one) (.name 2) (.const .zero) (.const .one) h⟩

abbrev expanded : Term Nat := .binary .mul (.name 7) (.name 8)
abbrev projection : Term Nat := .unary .fst (.binary .pair expanded (.const .bottom))
abbrev disjointSource : Term Nat := .binary .mul projection (.binary .mul first second)
abbrev disjointFused : Term Nat := .binary .mul projection merged
abbrev disjointChanged : Term Nat := .binary .mul expanded (.binary .mul first second)

theorem disjoint_expansion_peak : ModuloStep disjointSource disjointFused ∧
    ModuloStep disjointSource disjointChanged ∧ JoinModulo disjointFused disjointChanged ∧
    expanded.mulFactors.card = 2 ∧ expanded.mulFactors ≠ {expanded.baseClass} := by
  have hf : OuterFusion disjointSource disjointFused := by
    apply OuterFusion.of_factors _ _ oldKey (.name 1) (.name 2) (.const .zero) (.const .one)
      {projection.baseClass}
    · simp only [Term.mulFactors, ciphertextPairFactors, Multiset.insert_eq_cons,
        Multiset.cons_add, Multiset.singleton_add]
      rw [Multiset.cons_swap projection.baseClass first.baseClass]
      exact congrArg (fun xs => first.baseClass ::ₘ xs) (Multiset.pair_comm _ _)
    · simp [Term.mulFactors, Multiset.add_comm]
  have hi : FactorStep disjointSource disjointChanged := by
    exact ⟨projection, expanded, ciphertextPairFactors oldKey (.name 1) (.name 2) (.const .zero) (.const .one),
      rfl, (RootStep.fst expanded (.const .bottom)).to_modulo, by simp [Term.mulFactors, ciphertextPairFactors],
      by simp [Term.mulFactors, ciphertextPairFactors]⟩
  have h := fusion_factor_peak_joined hf hi
  refine ⟨h.1, h.2.1, outer_fusion_modulo_peak_joined hf hi.to_modulo,
    by simp [Term.mulFactors], ?_⟩
  intro he
  have hc := congrArg Multiset.card he
  simp [Term.mulFactors] at hc

/-- A factor step can increase outer factor count; it cannot be relabelled a fusion. -/
theorem projection_expansion_is_factor_step : FactorStep projection expanded ∧
    ¬ OuterFusion projection expanded := by
  refine ⟨⟨projection, expanded, 0, rfl,
    (RootStep.fst expanded (.const .bottom)).to_modulo, by simp [Term.mulFactors], by simp⟩, ?_⟩
  intro h
  have hc := h.card_step
  simp [Term.mulFactors] at hc

/-- Non-key component reductions use the corresponding nonce/plaintext output positions. -/
theorem nonce_and_plaintext_peaks :
    JoinModulo (combinedCiphertext (.name 0) oldKey (.name 2) (.const .zero) (.const .one))
      (.binary .mul (.ternary .penc (.name 0) (.name 0) (.const .zero))
        (.ternary .penc (.name 0) (.name 2) (.const .one))) ∧
    JoinModulo (combinedCiphertext (.name 0) (.name 1) (.name 2) oldKey (.const .one))
      (.binary .mul (.ternary .penc (.name 0) (.name 1) (.name 0))
        (.ternary .penc (.name 0) (.name 2) (.const .one))) := by
  have hp := (RootStep.fst (V := Nat) (.name 0) (.const .bottom)).to_modulo
  exact ⟨fusion_ciphertext_peak_joined _ _ _ _ _
    (hp.context (.ternarySecond .penc (.name 0) .hole (.const .zero))),
    fusion_ciphertext_peak_joined _ _ _ _ _
      (hp.context (.ternaryThird .penc (.name 0) (.name 1) .hole))⟩

end ExplainableCrypto.Helios.Symbolic.MixedFusionSPOT
