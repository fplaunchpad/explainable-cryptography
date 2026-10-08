import ExplainableCrypto.Helios.Symbolic.GlobalConfluence
import ExplainableCrypto.Helios.Symbolic.RawNormalizationSPOT

namespace ExplainableCrypto.Helios.Symbolic.GlobalConfluenceSPOT
open RawNormalizationSPOT

abbrev source : Term Nat := .binary .mul
  (.binary .compose backgroundSource (.name 7))
  (.binary .add (projection 2) (.const .zero))
abbrev left : Term Nat := .binary .mul
  (.binary .compose (.name 0) (.name 7))
  (.binary .add (projection 2) (.const .zero))
abbrev right : Term Nat := .binary .mul
  (.binary .compose backgroundSource (.name 7))
  (.binary .add (.name 2) (.const .zero))
abbrev expected : Term Nat := .binary .mul
  (.binary .compose (.name 0) (.name 7))
  (.binary .add (.name 2) (.const .zero))

theorem mixed_peak_steps : ModuloStep source left ∧ ModuloStep source right ∧ left ≠ right :=
  ⟨background_source_modulo_step.context
    (.binaryLeft .mul (.binaryLeft .compose .hole (.name 7)) (.binary .add (projection 2) (.const .zero))),
    (RootStep.fst (.name 2) (.const .bottom)).to_modulo.context
      (.binaryRight .mul (.binary .compose backgroundSource (.name 7)) (.binaryLeft .add .hole (.const .zero))),
    by decide⟩

/-- Apply global confluence to a peak spanning all three AC operators. -/
theorem mixed_peak_joined : JoinModulo left right :=
  confluence_modulo source left right (.single mixed_peak_steps.1) (.single mixed_peak_steps.2.1)

/-- Independent routes pin the common descendant, including its retained zero. -/
theorem mixed_routes_expected : ModuloStep left expected ∧ ModuloStep right expected :=
  ⟨(RootStep.fst (.name 2) (.const .bottom)).to_modulo.context
    (.binaryRight .mul (.binary .compose (.name 0) (.name 7)) (.binaryLeft .add .hole (.const .zero))),
    background_source_modulo_step.context
      (.binaryLeft .mul (.binaryLeft .compose .hole (.name 7)) (.binary .add (.name 2) (.const .zero)))⟩

/-- Full E equality has a common reduct even when raw normalization misses it. -/
theorem background_join_and_raw_failure : JoinModulo backgroundSource (.name 0) ∧
    normalizeRaw backgroundSource = backgroundSource ∧
    ¬ BaseEq (normalizeRaw backgroundSource) (normalizeRaw (.name 0 : Term Nat)) :=
  ⟨(eqE_iff_join _ _).mp background_source_modulo_step.sound,
    background_source_normalizes_to_itself, raw_normalization_incomplete_modulo.2.2⟩

theorem names_not_universally_equal : ¬ EqE (Term.name 0 : Term Nat) (.name 1) := by
  intro h
  have he := (irreducible_eqE_iff_base (name_irreducible 0) (name_irreducible 1)).mp h
  cases he.head_eq

theorem zero_one_not_collapsed : ¬ EqE (Term.const .zero : Term Nat) (.const .one) := by
  intro h
  have he := (irreducible_eqE_iff_base (constant_irreducible .zero) (constant_irreducible .one)).mp h
  have hn := congrArg AddSummary.numeric he.add_summary
  cases hn

theorem factor_weight_not_strict (n : Nat) :
    (Term.name (V := Nat) n).cryptoWeight =
      (Term.binary .mul (.name n) (.const .zero) : Term Nat).cryptoWeight := rfl

end ExplainableCrypto.Helios.Symbolic.GlobalConfluenceSPOT
