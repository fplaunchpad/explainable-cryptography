import ExplainableCrypto.Helios.Symbolic.ProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic.ProjectionPathSPOT

abbrev keyProjection : Term Nat := .unary .fst (.binary .pair (.name 0) (.const .bottom))
abbrev cipher : Term Nat := .ternary .penc (.unary .pk (.name 0)) (.name 1) (.const .one)
abbrev pairRevealed : Term Nat := .binary .pair cipher (.name 9)
abbrev reveal : Term Nat := .unary .fst (.binary .pair pairRevealed (.const .bottom))

theorem reducible_public_key : EqE (.unary .pk keyProjection) (.unary .pk (.name 0)) ∧
    ¬ BaseEq (.unary .pk keyProjection) (.unary .pk (.name 0)) := by
  refine ⟨(EqE.pk_iff _ _).mpr (RootStep.fst (.name 0) (.const .bottom)).to_modulo.sound, ?_⟩
  intro h
  have he := ((BaseEq.unary_iff _ _ _ _).mp h).2
  cases he.head_eq

theorem different_public_keys : ¬ EqE (Term.unary .pk (.name 0) : Term Nat) (.unary .pk (.name 1)) := by
  intro h
  have bad := (EqE.name_iff 0 1).mp ((EqE.pk_iff _ _).mp h)
  cases bad

theorem public_key_not_ciphertext : ¬ EqE (.unary .pk keyProjection) cipher := pk_not_eqE_penc _ _ _ _

theorem reveal_pair_step : ModuloStep reveal pairRevealed :=
  (RootStep.fst pairRevealed (.const .bottom)).to_modulo

theorem nested_projection_routes : ReducesModulo (.unary .fst reveal) cipher ∧
    ReducesModulo (.unary .snd reveal) (.name 9) :=
  ⟨(ReducesModulo.single (reveal_pair_step.context (.unary .fst .hole))).trans
    (.single (RootStep.fst cipher (.name 9)).to_modulo),
    (ReducesModulo.single (reveal_pair_step.context (.unary .snd .hole))).trans
      (.single (RootStep.snd cipher (.name 9)).to_modulo)⟩

theorem nested_projection_inversion : ∃ x y, ReducesModulo reveal (.binary .pair x y) ∧ EqE x cipher := by
  simpa using nested_projection_routes.1.sound.projection_penc_inversion (Or.inl rfl)

theorem initial_pair_shape_refuted : EqE (.unary .fst reveal) cipher ∧
    ¬ (∃ x y, reveal = .binary .pair x y) := by
  refine ⟨nested_projection_routes.1.sound, ?_⟩
  rintro ⟨x, y, h⟩
  cases h

theorem stuck_name_projection_not_cipher (n : Nat) :
    ¬ EqE (.unary .fst (.name n)) cipher := by
  intro h
  obtain ⟨x, y, hp, _⟩ := h.projection_penc_inversion (Or.inl rfl)
  have hh := ((name_irreducible n).reducesModulo hp).head_eq
  cases hh

theorem empty_projection_path :
    (∃ a', ReducesModulo (Term.name 4 : Term Nat) a' ∧
      BaseEq (.unary .fst (.name 4)) (.unary .fst a')) ∨
    (∃ x y, ReducesModulo (Term.name 4 : Term Nat) (.binary .pair x y) ∧
      ReducesModulo x (.unary .fst (.name 4))) := by
  simpa using (ReducesModulo.refl (Term.unary .fst (.name 4) : Term Nat)).projection_cases (Or.inl rfl)

private theorem normal_key_irreducible : Irreducible (Term.unary .pk (.name 0) : Term Nat) := by
  intro t h
  obtain ⟨a, ha, _⟩ := h.pk_cases
  exact name_irreducible 0 a ha

theorem normal_public_key_shape : ∃ a : Term Nat,
    Term.unary .pk (.name 0) = .unary .pk a ∧ EqE keyProjection a :=
  reducible_public_key.1.pk_irreducible_shape normal_key_irreducible

end ExplainableCrypto.Helios.Symbolic.ProjectionPathSPOT
