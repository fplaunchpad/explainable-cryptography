import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.BaseStructure

namespace ExplainableCrypto.Helios.Symbolic.RawNormalizationSPOT

abbrev projection (n : Nat) : Term Nat := .unary .fst (.binary .pair (.name n) (.const .bottom))

/-- Independent disjoint-position fixture, with the literal common descendant exposed. -/
theorem disjoint_projection_join :
    let source : Term Nat := .binary .pair (projection 0) (projection 1)
    let left : Term Nat := .binary .pair (.name 0) (projection 1)
    let right : Term Nat := .binary .pair (projection 0) (.name 1)
    let target : Term Nat := .binary .pair (.name 0) (.name 1)
    RewriteStep source left ∧ RewriteStep source right ∧
      RawReduces left target ∧ RawReduces right target ∧ normalizeRaw source = target := by
  dsimp
  exact ⟨(RootStep.fst (.name 0) (.const .bottom)).to_rewrite.context
      (.binaryLeft .pair .hole (projection 1)),
    (RootStep.fst (.name 1) (.const .bottom)).to_rewrite.context
      (.binaryRight .pair (projection 0) .hole),
    .single ((RootStep.fst (.name 1) (.const .bottom)).to_rewrite.context
      (.binaryRight .pair (.name 0) .hole)),
    .single ((RootStep.fst (.name 0) (.const .bottom)).to_rewrite.context
      (.binaryLeft .pair .hole (.name 1))), by decide⟩

/-- Root decryption competes with projection inside its plaintext. -/
theorem nested_decryption_join :
    let source : Term Nat := .binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.name 1) (projection 2))
    let inner : Term Nat := .binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.name 1) (.name 2))
    RewriteStep source (projection 2) ∧ RewriteStep source inner ∧
      RawReduces (projection 2) (.name 2) ∧ RawReduces inner (.name 2) ∧
      normalizeRaw source = .name 2 := by
  dsimp
  exact ⟨(RootStep.decrypt (.name 0) (.name 1) (projection 2)).to_rewrite,
    (RootStep.fst (.name 2) (.const .bottom)).to_rewrite.context
      (.binaryRight .dec (.name 0) (.ternaryThird .penc (.unary .pk (.name 0)) (.name 1) .hole)),
    .single (RootStep.fst (.name 2) (.const .bottom)).to_rewrite,
    .single (RootStep.decrypt (.name 0) (.name 1) (.name 2)).to_rewrite, by decide⟩

abbrev backgroundSource : Term Nat :=
  .binary .dec (.const .one)
    (.ternary .penc (.unary .pk (.binary .add (.const .zero) (.const .one))) (.name 1) (.name 0))

theorem background_source_modulo_step : ModuloStep backgroundSource (.name 0) :=
  (RootStep.decrypt (.const .one) (.name 1) (.name 0)).to_modulo.pre_base
    (.binary .dec (.refl _) (.ternary .penc (.unary .pk (.equation .zero_one)) (.refl _) (.refl _)))

theorem background_source_normalizes_to_itself : normalizeRaw backgroundSource = backgroundSource := by
  decide

theorem background_source_raw_irreducible : RawIrreducible backgroundSource := by
  simpa only [background_source_normalizes_to_itself] using normalizeRaw_irreducible backgroundSource

/-- The normalized endpoints of a modulo step need not even be E0-equal.
This is stronger than the failure of literal canonical representatives. -/
theorem raw_normalization_incomplete_modulo :
    ModuloStep backgroundSource (.name 0) ∧ RawIrreducible backgroundSource ∧
      ¬ BaseEq (normalizeRaw backgroundSource) (normalizeRaw (.name 0 : Term Nat)) := by
  refine ⟨background_source_modulo_step, background_source_raw_irreducible, ?_⟩
  intro he
  have hh := he.head_eq
  change (HeadTag.binary .dec : HeadTag Nat) = .name 0 at hh
  cases hh

end ExplainableCrypto.Helios.Symbolic.RawNormalizationSPOT
