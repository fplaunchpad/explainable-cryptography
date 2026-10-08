import ExplainableCrypto.Helios.Symbolic.TernaryStepCases

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Existing E8/E9 patterns, not new public operations. -/
abbrev bitCiphertext (k r : Term V) (bit : Constant) : Term V := .ternary .penc k r (.const bit)
abbrev bitProof (k r : Term V) (bit : Constant) : Term V :=
  .spk k r (.const bit) (bitCiphertext k r bit)

theorem RootStep.check_bit (k r : Term V) (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    RootStep (.ternary .checkspk k (bitCiphertext k r bit) (bitProof k r bit)) (.const .ok) := by
  rcases hb with rfl | rfl
  · exact .check_zero k r
  · exact .check_one k r

theorem ReducesModulo.bitCiphertext {k k' r r' : Term V}
    (hk : ReducesModulo k k') (hr : ReducesModulo r r') (bit : Constant) :
    ReducesModulo (bitCiphertext k r bit) (bitCiphertext k' r' bit) :=
  .ternary .penc hk hr (.refl _)

theorem ReducesModulo.bitProof {k k' r r' : Term V}
    (hk : ReducesModulo k k') (hr : ReducesModulo r r') (bit : Constant) :
    ReducesModulo (bitProof k r bit) (bitProof k' r' bit) :=
  .spk hk hr (.refl _) (hk.bitCiphertext hr bit)

/-- The constant vote field cannot take an oriented step, even modulo E0. -/
theorem ModuloStep.bitCiphertext_parameters {k r t : Term V} (bit : Constant)
    (h : ModuloStep (bitCiphertext k r bit) t) :
    ∃ k' r', BaseEq t (bitCiphertext k' r' bit) ∧ ReducesModulo k k' ∧ ReducesModulo r r' := by
  rcases h.penc_cases with ⟨k', hk, he⟩ | ⟨r', hr, he⟩ | ⟨m', hm, _⟩
  · exact ⟨k', r, he, .single hk, .refl _⟩
  · exact ⟨k, r', he, .refl _, .single hr⟩
  · exact False.elim (constant_irreducible bit m' hm)

/-- A changed proof need not already match its bound ciphertext. It can reduce
to a synchronized proof, preserving the immutable vote field. -/
theorem ModuloStep.bitProof_parameters {k r t : Term V} (bit : Constant)
    (h : ModuloStep (bitProof k r bit) t) :
    ∃ k' r', ReducesModulo k k' ∧ ReducesModulo r r' ∧ ReducesModulo t (bitProof k' r' bit) := by
  rcases h.spk_cases with ⟨k', hk, he⟩ | ⟨r', hr, he⟩ | ⟨m', hm, _⟩ | ⟨c', hc, he⟩
  · refine ⟨k', r, .single hk, .refl _, ?_⟩
    exact (ReducesModulo.spk (.refl k') (.refl r) (.refl (.const bit))
      ((ReducesModulo.single hk).bitCiphertext (.refl r) bit)).pre_base he
  · refine ⟨k, r', .refl _, .single hr, ?_⟩
    exact (ReducesModulo.spk (.refl k) (.refl r') (.refl (.const bit))
      ((ReducesModulo.refl k).bitCiphertext (.single hr) bit)).pre_base he
  · exact False.elim (constant_irreducible bit m' hm)
  · obtain ⟨k', r', hc', hk, hr⟩ := hc.bitCiphertext_parameters bit
    refine ⟨k', r', hk, hr, ?_⟩
    exact (ReducesModulo.spk hk hr (.refl (.const bit)) (.refl (bitCiphertext k' r' bit))).pre_base
      (he.trans (.spk (.refl _) (.refl _) (.refl _) hc'))

/-- Synchronize the ballot, proof metadata and proof-bound ciphertext after an
external key change, then apply the actual zero/one checking rule. -/
theorem check_key_step_reduces (k r : Term V) (bit : Constant) (hb : bit = .zero ∨ bit = .one)
    {k' : Term V} (hk : ModuloStep k k') :
    ReducesModulo (.ternary .checkspk k' (bitCiphertext k r bit) (bitProof k r bit)) (.const .ok) :=
  (ReducesModulo.ternary .checkspk (.refl k')
    ((ReducesModulo.single hk).bitCiphertext (.refl r) bit)
    ((ReducesModulo.single hk).bitProof (.refl r) bit)).trans
      (.single (RootStep.check_bit k' r bit hb).to_modulo)

/-- A change in the external ballot synchronizes the external key and whole proof. -/
theorem check_ballot_step_reduces (k r : Term V) (bit : Constant) (hb : bit = .zero ∨ bit = .one)
    {t : Term V} (h : ModuloStep (bitCiphertext k r bit) t) :
    ReducesModulo (.ternary .checkspk k t (bitProof k r bit)) (.const .ok) := by
  obtain ⟨k', r', he, hk, hr⟩ := h.bitCiphertext_parameters bit
  exact ((ReducesModulo.ternary .checkspk hk (.refl (bitCiphertext k' r' bit))
    (hk.bitProof hr bit)).trans (.single (RootStep.check_bit k' r' bit hb).to_modulo)).pre_base
      (.ternary .checkspk (.refl _) he (.refl _))

/-- A change anywhere inside the proof synchronizes all external occurrences too. -/
theorem check_proof_step_reduces (k r : Term V) (bit : Constant) (hb : bit = .zero ∨ bit = .one)
    {t : Term V} (h : ModuloStep (bitProof k r bit) t) :
    ReducesModulo (.ternary .checkspk k (bitCiphertext k r bit) t) (.const .ok) := by
  obtain ⟨k', r', hk, hr, ht⟩ := h.bitProof_parameters bit
  exact (ReducesModulo.ternary .checkspk hk (hk.bitCiphertext hr bit) ht).trans
    (.single (RootStep.check_bit k' r' bit hb).to_modulo)

end ExplainableCrypto.Helios.Symbolic
