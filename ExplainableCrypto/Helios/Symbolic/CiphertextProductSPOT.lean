import ExplainableCrypto.Helios.Symbolic.HistoricalCiphertextProducts
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT
import ExplainableCrypto.Helios.Symbolic.DecryptionPathSPOT

namespace ExplainableCrypto.Helios.Symbolic.CiphertextProductSPOT
open Historical

abbrev ns := HistoricalFrameSPOT.names
abbrev fr := frame ns false 0 1
abbrev honest : Recipe 3 := .unary .fst (.var 1)
abbrev constructed : Recipe 3 := .ternary .penc (.var 0) (.name 40) (.const .zero)
abbrev mixed : Recipe 3 := .binary .mul (.binary .mul constructed honest) honest
abbrev message : Recipe 3 := .binary .add (.binary .add (.const .zero) (.const .one)) (.const .one)
abbrev randomness : Ground := .binary .compose (.binary .compose (.name 40) (.name 20)) (.name 20)
abbrev c : Ground := .ternary .penc (publicKey ns) (.name 20) (.const .one)

private theorem honest_projection : ReducesModulo (fr.eval honest) c :=
  .single (RootStep.fst c (Term.tuple ((ballotFields ns 0 0).drop 1))).to_modulo

theorem honest_leaf : CiphertextProduct fr.value (publicKey ns) honest (.const .one) (.name 20) :=
  honest_component_product ns false 0 1 honest 0 0 honest_projection.sound

theorem swapped_projection_leaf :
    CiphertextProduct (frame ns true 0 1).value (publicKey ns)
      ((Term.var 2 : Recipe 3).project 1) (.const .zero) (.name 23) :=
  honest_projection_product ns true 0 1 1 1

theorem constructed_leaf : CiphertextProduct fr.value (publicKey ns) constructed (.const .zero) (.name 40) :=
  .constructed _ _ _ (.refl _)

theorem mixed_certificate : CiphertextProduct fr.value (publicKey ns) mixed message randomness :=
  .mul (.mul constructed_leaf honest_leaf) honest_leaf

/-- The repeated component contributes twice, in both the message and nonce trees. -/
theorem mixed_expected : EqE (fr.eval mixed)
      (.ternary .penc (.unary .pk (.name 10)) randomness
        (.binary .add (.binary .add (.const .zero) (.const .one)) (.const .one))) ∧
    message.Public ns.nonceNames ∧ message.nodeCount < mixed.nodeCount := by
  refine ⟨mixed_certificate.sound, mixed_certificate.plaintext_public ?_, mixed_certificate.plaintext_smaller⟩
  change ((True ∧ 40 ∉ ns.nonceNames ∧ True) ∧ True) ∧ True
  decide

abbrev doubled : Recipe 3 := .binary .mul honest honest
abbrev two : Ground := .binary .add (.const .one) (.const .one)
abbrev doubleNonce : Ground := .binary .compose (.name 20) (.name 20)

theorem doubled_certificate :
    CiphertextProduct fr.value (publicKey ns) doubled (.binary .add (.const .one) (.const .one)) doubleNonce :=
  .mul honest_leaf honest_leaf

private theorem doubled_path :
    ReducesModulo (fr.eval doubled) (keyCiphertext (.name 10) doubleNonce two) :=
  (ReducesModulo.binary .mul honest_projection honest_projection).trans
    (.single (RootStep.homomorphic (publicKey ns) (.name 20) (.name 20) (.const .one) (.const .one)).to_modulo)

/-- This valid nonce-public decryption succeeds but cannot be minimum. -/
theorem repeated_component_decrypts_two :
    (.binary .dec (.name 10) doubled : Recipe 3).Public ns.nonceNames ∧
      EqE (fr.eval (.binary .dec (.name 10) doubled)) two ∧
      ¬ MinimalRecipe ns.nonceNames fr.value (.binary .dec (.name 10) doubled) := by
  have hm : DecryptionMatch (fr.eval (.name 10)) (fr.eval doubled) two :=
    ⟨.name 10, doubleNonce, Or.inl (.refl _), doubled_path⟩
  refine ⟨?_, hm.reduces.sound, ?_⟩
  · change 10 ∉ ns.nonceNames ∧ True ∧ True
    decide
  · intro hmin
    exact doubled_certificate.no_minimum_decryption_match (.name 10) hmin two hm

/-- Kernel-checked full-E version of the gate's duplicate-collapse counterexample. -/
theorem duplicate_collapse_rejected :
    ¬ EqE (fr.eval doubled) (.ternary .penc (publicKey ns) doubleNonce (.const .one)) := by
  intro he
  have hm := ((EqE.penc_iff _ _ _ _ _ _).mp (doubled_certificate.sound.symm.trans he)).2.2
  exact two_not_one hm

/-- Sound certificates cannot silently change the public key, even at a constant leaf. -/
theorem wrong_key_rejected (p : Recipe 3) (nonce : Ground) :
    ¬ CiphertextProduct fr.value (publicKey ns)
      (.ternary .penc (.name 99) (.name 40) (.const .zero)) p nonce := by
  intro h
  have hk := ((EqE.penc_iff _ _ _ _ _ _).mp h.sound).1
  obtain ⟨_, hh, _⟩ := hk.symm.pk_irreducible_shape (name_irreducible 99)
  cases hh

/-- A one-node ciphertext handle has no strictly smaller plaintext recipe.
This refutes treating the product certificate as universal provenance. -/
theorem published_ciphertext_size_boundary (p : Recipe 1) (nonce : Ground) :
    EqE ((Term.var 0 : Recipe 1).subst (fun _ => c)) c ∧
      ¬ CiphertextProduct (fun _ : Fin 1 => c) (publicKey ns) (.var 0) p nonce := by
  refine ⟨.refl _, ?_⟩
  intro h
  have hs := h.plaintext_smaller
  have hp := p.nodeCount_pos
  simp only [Term.nodeCount] at hs
  omega

/-- The normal-form theorem's minimum premise is inhabited by a stuck constructed leaf. -/
theorem minimum_control :
    BaseEq DecryptionPathSPOT.stuck (.binary .dec (.var 0) DecryptionPathSPOT.stuckCipher) := by
  have hc : CiphertextProduct (Term.var : Nat → Term Nat) (.var 1)
      DecryptionPathSPOT.stuckCipher (.var 3) (.var 2) := .constructed _ _ _ (.refl _)
  have hb := DecryptionPathSPOT.stuck_irreducible.context_hole (.binaryRight .dec (.var 0) .hole)
  exact hc.minimum_decryption_normal_form (.var 0) DecryptionPathSPOT.stuck_minimal
    (var_irreducible 0) hb DecryptionPathSPOT.stuck_irreducible (.refl _) (.refl _) (.refl _)

end ExplainableCrypto.Helios.Symbolic.CiphertextProductSPOT
