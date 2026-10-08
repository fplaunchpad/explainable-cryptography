import ExplainableCrypto.Helios.Symbolic.MultiplicationHeads
import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.Separation

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationInversionSPOT

abbrev reveal (t : Term Nat) : Term Nat := .unary .fst (.binary .pair t (.const .bottom))
abbrev c₀ : Term Nat := .ternary .penc (.name 0) (.name 10) (.name 40)
abbrev c₁ : Term Nat := .ternary .penc (.name 0) (.name 11) (.name 41)
abbrev c₂ : Term Nat := .ternary .penc (.name 0) (.name 12) (.name 42)
abbrev a := reveal (.binary .mul c₀ c₁)
abbrev b := reveal c₂
abbrev source : Term Nat := .binary .mul a b
abbrev leftValue : Term Nat := .ternary .penc (.name 0)
  (.binary .compose (.name 10) (.name 11)) (.binary .add (.name 40) (.name 41))
abbrev expected : Term Nat := .ternary .penc (.name 0)
  (.binary .compose (.binary .compose (.name 10) (.name 11)) (.name 12))
  (.binary .add (.binary .add (.name 40) (.name 41)) (.name 42))

private theorem revealed (t : Term Nat) : ReducesModulo (reveal t) t :=
  .single (RootStep.fst t (.const .bottom)).to_modulo

theorem left_operand_value : ReducesModulo a leftValue :=
  (revealed _).trans (.single (RootStep.homomorphic (.name 0) (.name 10) (.name 11) (.name 40) (.name 41)).to_modulo)

theorem product_reaches_expected : ReducesModulo source expected :=
  (ReducesModulo.binary .mul left_operand_value (revealed _)).trans
    (.single (RootStep.homomorphic (.name 0) (.binary .compose (.name 10) (.name 11))
      (.name 12) (.binary .add (.name 40) (.name 41)) (.name 42)).to_modulo)

/-- The first factor is initially a projection and expands into two outer factors. -/
theorem expanding_factor_step :
    ModuloStep source (.binary .mul (.binary .mul c₀ c₁) b) ∧
      source.mulFactors.card = 2 ∧
      (Term.binary .mul (.binary .mul c₀ c₁) b).mulFactors.card = 3 := by
  refine ⟨(RootStep.fst (.binary .mul c₀ c₁) (.const .bottom)).to_modulo.context
    (.binaryLeft .mul .hole b), ?_, ?_⟩ <;> simp [a, b, reveal, Term.mulFactors]

/-- The general inverse retains both operand values and the exact aggregate equations. -/
theorem expanding_product_inversion :
    ∃ r s m n, EqE a (.ternary .penc (.name 0) r m) ∧
      EqE b (.ternary .penc (.name 0) s n) ∧
      EqE (.binary .compose r s) (.binary .compose (.binary .compose (.name 10) (.name 11)) (.name 12)) ∧
      EqE (.binary .add m n) (.binary .add (.binary .add (.name 40) (.name 41)) (.name 42)) :=
  product_reaches_expected.sound.mul_penc_inversion

/-- Fixed constructor values are independent witnesses for the inverse's existential fields. -/
theorem expected_operands_reconstruct : EqE source expected := by
  apply (EqE.mul_penc_iff _ _ _ _ _).mpr
  exact ⟨.binary .compose (.name 10) (.name 11), .name 12,
    .binary .add (.name 40) (.name 41), .name 42,
    left_operand_value.sound, (revealed _).sound, .refl _, .refl _⟩

theorem different_keys_rejected (key nonce message : Term Nat) :
    ¬ EqE (.binary .mul c₀ (.ternary .penc (.name 1) (.name 11) (.name 41)))
      (.ternary .penc key nonce message) := by
  apply unequal_keys_product_not_ciphertext
  intro h
  have he := (EqE.name_iff 0 1).mp h
  cases he

theorem unrelated_factor_retained (key nonce message : Term Nat) :
    ¬ EqE (.binary .mul c₀ (.name 99)) (.ternary .penc key nonce message) :=
  name_factor_not_ciphertext _ _ _ _ _

abbrev e0Source : Term Nat := .binary .mul
  (.ternary .penc (.binary .add (.const .zero) (.const .one)) (.name 10) (.name 40))
  (.ternary .penc (.const .one) (.name 11) (.name 41))
abbrev e0Expected : Term Nat := .ternary .penc (.const .one)
  (.binary .compose (.name 10) (.name 11)) (.binary .add (.name 40) (.name 41))

/-- Raw matching failure on E0-equal keys does not decide full-E ciphertext value. -/
theorem e0_keys_match_beyond_raw : EqE e0Source e0Expected ∧
    normalizeRaw e0Source = e0Source ∧ ¬ BaseEq e0Source e0Expected := by
  refine ⟨?_, by decide, ?_⟩
  · exact (EqE.binary .mul (.ternary .penc (.equation .zero_one) (.refl _) (.refl _)) (.refl _)).trans
      (RootStep.homomorphic (.const .one) (.name 10) (.name 11) (.name 40) (.name 41)).sound
  · intro h
    cases h.head_eq

theorem repeated_plaintext_retained :
    let c : Term Nat := .ternary .penc (.name 0) (.name 10) (.const .one)
    ¬ EqE (.binary .mul c c) (.ternary .penc (.name 0)
      (.binary .compose (.name 10) (.name 10)) (.const .one)) := by
  dsimp only
  intro h
  have he := (RootStep.homomorphic (.name 0) (.name 10) (.name 10) (.const .one) (.const .one)).sound.symm.trans h
  exact two_not_one ((EqE.penc_iff _ _ _ _ _ _).mp he).2.2

/-- Passive target constructors may contain reducible terms; exclusion is still full E. -/
theorem passive_outputs_rejected :
    ¬ EqE source (.binary .pair (reveal (.name 7)) (reveal (.name 8))) ∧
    ¬ EqE source (.binary .partialDecrypt (reveal (.name 7)) (reveal (.name 8))) ∧
    ¬ EqE source (.spk a b a b) ∧ ¬ EqE source (.unary .pk a) :=
  ⟨mul_not_eqE_passive_binary _ _ _ _ .pair (Or.inl rfl),
    mul_not_eqE_passive_binary _ _ _ _ .partialDecrypt (Or.inr rfl),
    mul_not_eqE_spk _ _ _ _ _ _, mul_not_eqE_pk _ _ _⟩

/-- Even zero remains an ordinary multiplication factor, not an identity. -/
theorem zero_is_not_multiplication_unit :
    ¬ EqE (Term.binary (V := Nat) .mul (.const .zero) (.const .zero)) (.const .zero) :=
  mul_not_eqE_constant _ _ _

/-- The product-head branch is inhabited by an actual reachable normal value. -/
theorem noncipher_product_normal_head :
    ∃ t : Term Nat, ReducesModulo (.binary .mul (.name 0) (.name 1)) t ∧
      Irreducible t ∧ ∃ x y, t = .binary .mul x y := by
  obtain ⟨t, ht, hi⟩ := exists_normal_form (Term.binary (V := Nat) .mul (.name 0) (.name 1))
  rcases ht.sound.mul_irreducible_shape hi with hm | ⟨k, r, m, he⟩
  · exact ⟨t, ht.to_modulo, hi, hm⟩
  · subst t
    exact False.elim (name_factor_not_ciphertext _ _ _ _ _ ht.sound)

/-- Dropping target normality admits an equivalent projection head. -/
theorem normality_required_for_product_shape :
    EqE source (reveal expected) ∧
      ¬ ((∃ x y, reveal expected = .binary .mul x y) ∨
        (∃ k r m, reveal expected = .ternary .penc k r m)) ∧
      ¬ Irreducible (reveal expected) := by
  refine ⟨product_reaches_expected.sound.trans (revealed _).sound.symm, ?_, ?_⟩
  · rintro (⟨x, y, he⟩ | ⟨k, r, m, he⟩) <;> cases he
  · exact fun h => h expected (RootStep.fst expected (.const .bottom)).to_modulo

end ExplainableCrypto.Helios.Symbolic.MultiplicationInversionSPOT
