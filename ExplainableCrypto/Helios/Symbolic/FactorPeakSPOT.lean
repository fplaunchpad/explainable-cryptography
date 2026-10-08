import ExplainableCrypto.Helios.Symbolic.CiphertextLocalConfluence

namespace ExplainableCrypto.Helios.Symbolic.FactorPeakSPOT

/-- A retained counterexample to using crypto weight alone for factor recursion. -/
theorem factor_weight_need_not_decrease :
    (Term.name 0 : Term Nat).cryptoWeight =
      (Term.binary .mul (.name 0) (.const .zero) : Term Nat).cryptoWeight ∧
    (Term.binary .mul (.name 0) (.const .zero) : Term Nat).mulFactors.card = 2 := by
  decide

/-- Equal selected classes leave equal residuals without erasing their other copy. -/
theorem repeated_singleton_selection :
    ({0, 0, 1} : Multiset Nat) = {0} + {0, 1} ∧
    ((0 : Nat) = 0 ∧ ({0, 1} : Multiset Nat) = {0, 1}) ∧
    ({0, 0, 1} : Multiset Nat).card = 3 := by decide

abbrev outA : Term Nat := .binary .mul (.name 1) (.name 2)
abbrev outB : Term Nat := .binary .mul (.name 3) (.name 4)
abbrev a : Term Nat := .unary .fst (.binary .pair outA (.const .bottom))
abbrev b : Term Nat := .unary .snd (.binary .pair (.const .bottom) outB)
abbrev source : Term Nat := .binary .mul (.binary .mul a (.name 9)) b
abbrev left : Term Nat := .binary .mul (.binary .mul outA (.name 9)) b
abbrev right : Term Nat := .binary .mul (.binary .mul a (.name 9)) outB
abbrev expected : Term Nat := .binary .mul (.binary .mul outA (.name 9)) outB

private theorem factor_swap (a b c : Multiset (BaseClass Nat)) : a + (b + c) = b + (a + c) := by
  rw [← Multiset.add_assoc, Multiset.add_comm a b, Multiset.add_assoc]

/-- Both disjoint replacements expand into two factors and retain the unrelated name. -/
theorem disjoint_expanding_projections :
    ModuloStep source left ∧ ModuloStep source right ∧ JoinModulo left right ∧
    left.mulFactors.card = 4 ∧ right.mulFactors.card = 4 ∧
    expected.mulFactors.card = 5 ∧ left ≠ right := by
  have h := disjoint_factor_reductions_joined source left right a outA b outB
    {(Term.name 9 : Term Nat).baseClass}
    (RootStep.fst outA (.const .bottom)).to_modulo
    (RootStep.snd (.const .bottom) outB).to_modulo
    (by simp only [Term.mulFactors, Multiset.add_assoc, Multiset.add_comm, factor_swap])
    (by simp only [Term.mulFactors, Multiset.add_assoc, Multiset.add_comm])
    (by simp only [Term.mulFactors, Multiset.add_assoc, Multiset.add_comm])
  exact ⟨h.1, h.2.1, h.2.2, by decide, by decide, by decide, by decide⟩

/-- Independently fixed common descendant, with neither output product collapsed. -/
theorem disjoint_routes_expected : ModuloStep left expected ∧ ModuloStep right expected :=
  ⟨(RootStep.snd (.const .bottom) outB).to_modulo.context
    (.binaryRight .mul (.binary .mul outA (.name 9)) .hole),
    (RootStep.fst outA (.const .bottom)).to_modulo.context
      (.binaryLeft .mul (.binaryLeft .mul .hole (.name 9)) outB)⟩

abbrev key : Term Nat := .unary .fst (.binary .pair (.name 0) (.const .bottom))
abbrev nonce : Term Nat := .unary .snd (.binary .pair (.const .bottom) (.name 1))
abbrev plain : Term Nat := .binary .add (.const .zero) (.const .zero)
abbrev sameSource : Term Nat := .binary .mul (.ternary .penc key nonce plain) (.name 9)
abbrev sameLeft : Term Nat := .binary .mul (.ternary .penc (.name 0) nonce (.const .zero)) (.name 9)
abbrev sameRight : Term Nat := .binary .mul (.ternary .penc key (.name 1) plain) (.name 9)
abbrev sameExpected : Term Nat := .binary .mul (.ternary .penc (.name 0) (.name 1) (.const .zero)) (.name 9)

/-- Same factor, different components and E0 representatives: both specified
branches take an actual step to the same independently stated ciphertext. -/
theorem same_factor_component_peak :
    ModuloStep sameSource sameLeft ∧ ModuloStep sameSource sameRight ∧
    ModuloStep sameLeft sameExpected ∧ ModuloStep sameRight sameExpected ∧
    sameLeft ≠ sameRight := by
  have hk := (RootStep.fst (V := Nat) (.name 0) (.const .bottom)).to_modulo
  have hr := (RootStep.snd (V := Nat) (.const .bottom) (.name 1)).to_modulo
  have h := ciphertext_key_nonce_steps key (.name 0) nonce (.name 1) (.const .zero) hk hr
  have hb : BaseEq plain (.const .zero) := .equation .zero_zero
  refine ⟨(h.1.context (.binaryLeft .mul .hole (.name 9))).pre_base
    (.binary .mul (.ternary .penc (.refl _) (.refl _) hb) (.refl _)),
    hr.context (.binaryLeft .mul (.ternarySecond .penc key .hole plain) (.name 9)),
    h.2.2.1.context (.binaryLeft .mul .hole (.name 9)),
    (h.2.2.2.context (.binaryLeft .mul .hole (.name 9))).pre_base
      (.binary .mul (.ternary .penc (.refl _) (.refl _) hb) (.refl _)), by decide⟩

end ExplainableCrypto.Helios.Symbolic.FactorPeakSPOT
