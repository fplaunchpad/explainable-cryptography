import ExplainableCrypto.Helios.Symbolic.UnaryLocalConfluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Abbreviation for the existing E5/E6 ciphertext pattern, not a new constructor. -/
abbrev keyCiphertext (k r m : Term V) : Term V := .ternary .penc (.unary .pk k) r m

/-- pk has no root rule, so every step originates in its argument. -/
theorem ModuloStep.pk_cases {k t : Term V} (h : ModuloStep (.unary .pk k) t) :
    ∃ k', ModuloStep k k' ∧ BaseEq t (.unary .pk k') := by
  rcases h.unary_cases with hroot | hinner
  · rcases hroot.unary_projection_cases with ⟨_, _, hf, _⟩ | ⟨_, _, hf, _⟩ <;> cases hf
  · exact hinner

theorem ReducesModulo.keyCiphertext {k k' r r' m m' : Term V}
    (hk : ReducesModulo k k') (hr : ReducesModulo r r') (hm : ReducesModulo m m') :
    ReducesModulo (keyCiphertext k r m) (keyCiphertext k' r' m') :=
  .ternary .penc (.unary .pk hk) hr hm

/-- Any ciphertext step admits synchronized E5/E6 parameters. This is metatheory
inversion; it does not give an attacker the ciphertext's private-key argument. -/
theorem ModuloStep.keyCiphertext_parameters {k r m t : Term V}
    (h : ModuloStep (keyCiphertext k r m) t) :
    ∃ k' r' m', BaseEq t (keyCiphertext k' r' m') ∧
      ReducesModulo k k' ∧ ReducesModulo r r' ∧ ReducesModulo m m' := by
  rcases h.penc_cases with ⟨pk', hk, he⟩ | ⟨r', hr, he⟩ | ⟨m', hm, he⟩
  · obtain ⟨k', hkk, hpk⟩ := hk.pk_cases
    exact ⟨k', r, m, he.trans (.ternary .penc hpk (.refl _) (.refl _)),
      .single hkk, .refl _, .refl _⟩
  · exact ⟨k, r', m, he, .refl _, .single hr, .refl _⟩
  · exact ⟨k, r, m', he, .refl _, .refl _, .single hm⟩

/-- E5 versus a step in its explicit key argument. -/
theorem decrypt_key_step_joined (k r m : Term V) {k' : Term V} (hk : ModuloStep k k') :
    JoinModulo m (.binary .dec k' (keyCiphertext k r m)) := by
  refine ⟨m, .refl _, ?_⟩
  exact ((ReducesModulo.keyCiphertext (.single hk) (.refl r) (.refl m)).context
    (.binaryRight .dec k' .hole)).trans (.single (RootStep.decrypt k' r m).to_modulo)

/-- E5 versus any step in its ciphertext, including public-key, nonce and plaintext changes. -/
theorem decrypt_ciphertext_step_joined (k r m : Term V) {t : Term V}
    (h : ModuloStep (keyCiphertext k r m) t) : JoinModulo m (.binary .dec k t) := by
  obtain ⟨k', r', m', he, hk, _, hm⟩ := h.keyCiphertext_parameters
  refine ⟨m', hm, ?_⟩
  exact ((hk.context (.binaryLeft .dec .hole (keyCiphertext k' r' m'))).trans
    (.single (RootStep.decrypt k' r' m').to_modulo)).pre_base (.binary .dec (.refl _) he)

/-- E6 versus any step in its partial-decryption argument. All repeated key and
ciphertext copies follow the same supplied parameter reductions. -/
theorem partial_decrypt_left_step_joined (k r m : Term V) {t : Term V}
    (h : ModuloStep (.binary .partialDecrypt k (keyCiphertext k r m)) t) :
    JoinModulo m (.binary .dec t (keyCiphertext k r m)) := by
  rcases h.passive_binary_cases (Or.inr rfl) with ⟨k', hk, he⟩ | ⟨c', hc, he⟩
  · have henc := ReducesModulo.keyCiphertext (.single hk) (.refl r) (.refl m)
    refine ⟨m, .refl _, ?_⟩
    exact ((ReducesModulo.binary .dec
      (.binary .partialDecrypt (.refl k') henc) henc).trans
        (.single (RootStep.partial_decrypt k' r m).to_modulo)).pre_base
          (.binary .dec he (.refl _))
  · obtain ⟨k', r', m', hc', hk, hr, hm⟩ := hc.keyCiphertext_parameters
    have henc := ReducesModulo.keyCiphertext hk hr hm
    refine ⟨m', hm, ?_⟩
    exact ((ReducesModulo.binary .dec
      (.binary .partialDecrypt hk (.refl (keyCiphertext k' r' m'))) henc).trans
        (.single (RootStep.partial_decrypt k' r' m').to_modulo)).pre_base
          (.binary .dec (he.trans (.binary .partialDecrypt (.refl _) hc')) (.refl _))

/-- E6 versus any step in the right ciphertext. The left partial-decryption
argument synchronizes both its explicit key and its complete ciphertext copy. -/
theorem partial_decrypt_right_step_joined (k r m : Term V) {t : Term V}
    (h : ModuloStep (keyCiphertext k r m) t) :
    JoinModulo m (.binary .dec (.binary .partialDecrypt k (keyCiphertext k r m)) t) := by
  obtain ⟨k', r', m', he, hk, hr, hm⟩ := h.keyCiphertext_parameters
  have henc := ReducesModulo.keyCiphertext hk hr hm
  refine ⟨m', hm, ?_⟩
  exact ((ReducesModulo.binary .dec (.binary .partialDecrypt hk henc)
    (.refl (keyCiphertext k' r' m'))).trans
      (.single (RootStep.partial_decrypt k' r' m').to_modulo)).pre_base
        (.binary .dec (.refl _) he)

end ExplainableCrypto.Helios.Symbolic
