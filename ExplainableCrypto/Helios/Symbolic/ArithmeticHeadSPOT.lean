import ExplainableCrypto.Helios.Symbolic.ArithmeticSeparation
import ExplainableCrypto.Helios.Symbolic.ComposeFactorSPOT
import ExplainableCrypto.Helios.Symbolic.Separation

namespace ExplainableCrypto.Helios.Symbolic.ArithmeticHeadSPOT

abbrev reveal (t : Term Nat) : Term Nat := .unary .fst (.binary .pair t (.const .bottom))
abbrev expansionSource : Term Nat :=
  .binary .compose (reveal (.binary .compose (.name 1) (.name 2))) (.name 3)
abbrev expansionTarget : Term Nat := .binary .compose (.binary .compose (.name 1) (.name 2)) (.name 3)

/-- Composition permits factor expansion while retaining all three final occurrences. -/
theorem composition_expands : ModuloStep expansionSource expansionTarget ∧
    expansionSource.composeFactors.card = 2 ∧ expansionTarget.composeFactors.card = 3 := by
  refine ⟨(RootStep.fst (.binary .compose (.name 1) (.name 2)) (.const .bottom)).to_modulo.context
    (.binaryLeft .compose .hole (.name 3)), ?_, ?_⟩
  · simp [reveal, Term.composeFactors]
  · simp [Term.composeFactors]

theorem composition_path_shape : ∃ a b, expansionTarget = .binary .compose a b :=
  (ReducesModulo.single composition_expands.1).compose_shape

theorem composition_normal_shape :
    let t : Term Nat := .binary .compose (.name 1) (.name 2)
    Irreducible t ∧ ∃ a b, t = .binary .compose a b := by
  dsimp only
  have hp : EqE (.binary .compose (reveal (.name 1)) (.name 2) : Term Nat)
      (.binary .compose (.name 1) (.name 2)) :=
    .binary .compose (RootStep.fst (.name 1) (.const .bottom)).sound (.refl _)
  have hi := ComposeFactorSPOT.composed_names_irreducible 1 2
  exact ⟨hi, hp.compose_irreducible_shape hi⟩

/-- These are the actual E3/E4 numeric paths; their constant endpoints are irreducible. -/
theorem numeric_collapses :
    ReducesModulo (Term.binary (V := Nat) .add (.const .zero) (.const .one)) (.const .one) ∧
    ReducesModulo (Term.binary (V := Nat) .add (.const .zero) (.const .zero)) (.const .zero) ∧
    Irreducible (Term.const (V := Nat) .one) ∧ Irreducible (Term.const (V := Nat) .zero) :=
  ⟨.base (.equation .zero_one), .base (.equation .zero_zero),
    constant_irreducible .one, constant_irreducible .zero⟩

theorem literal_add_head_can_disappear :
    EqE (Term.binary (V := Nat) .add (.const .zero) (.const .zero)) (.const .zero) ∧
      ¬ (∃ a b : Term Nat, (Term.const .zero : Term Nat) = .binary .add a b) := by
  refine ⟨.equation .zero_zero, ?_⟩
  rintro ⟨a, b, he⟩
  cases he

abbrev sumSource : Term Nat := .binary .add (reveal (.const .zero)) (.name 7)
abbrev sumTarget : Term Nat := .binary .add (.const .zero) (.name 7)

/-- A factor can become zero, but the numeric presence remains beside the name. -/
theorem numeric_presence_retained : ModuloStep sumSource sumTarget ∧
    sumTarget.addSummary.numeric = some 0 ∧ sumTarget.addSummary.atoms = {(.name 7 : Term Nat).baseClass} ∧
    ¬ EqE sumTarget (.name 7) :=
  ⟨(RootStep.fst (.const .zero) (.const .bottom)).to_modulo.context (.binaryLeft .add .hole (.name 7)),
    rfl, rfl, arithmetic_not_eqE_name .add (Or.inl rfl) _ _ _⟩

theorem addition_path_shape :
    (∃ a b, sumTarget = .binary .add a b) ∨ sumTarget = .const .zero ∨ sumTarget = .const .one :=
  (ReducesModulo.single numeric_presence_retained.1).add_shape

theorem composition_has_no_zero_unit :
    ¬ EqE (Term.binary (V := Nat) .compose (.const .zero) (.name 7)) (.name 7) :=
  arithmetic_not_eqE_name .compose (Or.inr rfl) _ _ _

theorem composition_cannot_collapse_numeric :
    ¬ EqE (Term.binary (V := Nat) .compose (.const .zero) (.const .zero)) (.const .zero) := by
  intro h
  have hh := h.arithmetic_constant_cases (Or.inr rfl)
  cases hh.1

theorem two_ones_remain_two :
    ¬ EqE (Term.binary (V := Nat) .add (.const .one) (.const .one)) (.const .one) := two_not_one

/-- Both arithmetic heads exclude ciphertext and passive outputs with reducible components. -/
theorem arithmetic_outputs_excluded (f : Binary) (hf : f = .add ∨ f = .compose) :
    ¬ EqE (.binary f sumSource expansionSource) (.ternary .penc (reveal (.name 1)) (.name 2) (.name 3)) ∧
    ¬ EqE (.binary f sumSource expansionSource) (.binary .pair (reveal (.name 1)) (.name 2)) ∧
    ¬ EqE (.binary f sumSource expansionSource) (.binary .partialDecrypt (reveal (.name 1)) (.name 2)) ∧
    ¬ EqE (.binary f sumSource expansionSource) (.spk sumSource expansionSource sumSource expansionSource) ∧
    ¬ EqE (.binary f sumSource expansionSource) (.unary .pk (reveal (.name 1))) :=
  ⟨arithmetic_not_eqE_penc f hf _ _ _ _ _,
    arithmetic_not_eqE_passive_binary f .pair hf (Or.inl rfl) _ _ _ _,
    arithmetic_not_eqE_passive_binary f .partialDecrypt hf (Or.inr rfl) _ _ _ _,
    arithmetic_not_eqE_spk f hf _ _ _ _ _ _, arithmetic_not_eqE_pk f hf _ _ _⟩

theorem arithmetic_operations_distinct :
    ¬ EqE (.binary .compose sumSource expansionSource) (.binary .add sumSource expansionSource) ∧
    ¬ EqE (.binary .add sumSource expansionSource) (.binary .mul sumSource expansionSource) ∧
    ¬ EqE (.binary .compose sumSource expansionSource) (.binary .mul sumSource expansionSource) :=
  ⟨compose_not_eqE_add _ _ _ _, arithmetic_not_eqE_mul .add (Or.inl rfl) _ _ _ _,
    arithmetic_not_eqE_mul .compose (Or.inr rfl) _ _ _ _⟩

/-- E-equal reducible representatives can wrap a numeric result in a projection. -/
theorem normality_required_for_sum_shape :
    EqE (Term.binary (V := Nat) .add (.const .zero) (.const .one)) (reveal (.const .one)) ∧
    ¬ ((∃ a b, reveal (.const .one) = .binary .add a b) ∨
      reveal (.const .one) = .const .zero ∨ reveal (.const .one) = .const .one) ∧
    ¬ Irreducible (reveal (.const .one)) := by
  have hs := (RootStep.fst (.const (V := Nat) .one) (.const .bottom)).to_modulo
  refine ⟨(EqE.equation .zero_one).trans hs.sound.symm, ?_, fun h => h _ hs⟩
  rintro (⟨a, b, he⟩ | he | he) <;> cases he

end ExplainableCrypto.Helios.Symbolic.ArithmeticHeadSPOT
