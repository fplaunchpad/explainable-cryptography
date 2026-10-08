import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic.FullStructureSPOT

abbrev projection (n : Nat) : Term Nat := .unary .fst (.binary .pair (.name n) (.const .bottom))

private theorem project (n : Nat) : EqE (projection n) (.name n) :=
  (RootStep.fst (.name n) (.const .bottom)).to_modulo.sound

abbrev cipher : Term Nat := .ternary .penc (projection 0)
  (.binary .compose (.name 1) (.name 2)) (projection 3)
abbrev expected : Term Nat := .ternary .penc (.name 0)
  (.binary .compose (.name 2) (.name 1)) (.name 3)

theorem reducible_cipher_equality : EqE cipher expected ∧ ¬ BaseEq cipher expected := by
  refine ⟨(EqE.penc_iff _ _ _ _ _ _).mpr ⟨project 0,
    (BaseEq.equation (.comm .compose trivial _ _)).sound, project 3⟩, ?_⟩
  intro h
  have hk := ((BaseEq.penc_iff _ _ _ _ _ _).mp h).1
  cases hk.head_eq

theorem reducible_cipher_components : EqE (projection 0) (.name 0) ∧
    EqE (Term.binary .compose (.name 1) (.name 2) : Term Nat) (.binary .compose (.name 2) (.name 1)) ∧
    EqE (projection 3) (.name 3) :=
  (EqE.penc_iff _ _ _ _ _ _).mp reducible_cipher_equality.1

theorem ciphertext_changed_message_rejected :
    ¬ EqE cipher (.ternary .penc (.name 0) (.binary .compose (.name 2) (.name 1)) (.name 4)) := by
  intro h
  have hm := ((EqE.penc_iff _ _ _ _ _ _).mp h).2.2
  have bad := (EqE.name_iff 3 4).mp ((project 3).symm.trans hm)
  cases bad

theorem ciphertext_multiple_steps : ReducesModulo cipher expected := by
  have h₁ := (RootStep.fst (.name 0) (.const .bottom)).to_modulo.context
    (.ternaryFirst .penc .hole (.binary .compose (.name 1) (.name 2)) (projection 3))
  have h₂ := (RootStep.fst (V := Nat) (.name 3) (.const .bottom)).to_modulo.context
    (.ternaryThird .penc (.name 0) (.binary .compose (.name 1) (.name 2)) .hole)
  exact ((ReducesModulo.single h₁).trans (.single h₂)).post_base
    (.ternary .penc (.refl _) (.equation (.comm .compose trivial _ _)) (.refl _))

theorem ciphertext_path_components : ∃ k r m, BaseEq expected (.ternary .penc k r m) ∧
    ReducesModulo (projection 0) k ∧
    ReducesModulo (Term.binary .compose (.name 1) (.name 2) : Term Nat) r ∧
    ReducesModulo (projection 3) m := ciphertext_multiple_steps.penc_components

theorem reducible_proof_components : EqE
    (.spk (projection 0) (projection 1) (projection 2) (projection 3))
    (.spk (.name 0) (.name 1) (.name 2) (.name 3)) :=
  (EqE.spk_iff _ _ _ _ _ _ _ _).mpr ⟨project 0, project 1, project 2, project 3⟩

theorem proof_binding_change_rejected : ¬ EqE
    (.spk (projection 0) (projection 1) (projection 2) (projection 3))
    (.spk (.name 0) (.name 1) (.name 2) (.name 4)) := by
  intro h
  have hd := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp h).2.2.2
  have bad := (EqE.name_iff 3 4).mp ((project 3).symm.trans hd)
  cases bad

theorem pair_order_retained : EqE (.binary .pair (projection 0) (projection 1))
    (.binary .pair (.name 0) (.name 1)) ∧
    ¬ EqE (Term.binary .pair (.name 0) (.name 1) : Term Nat) (.binary .pair (.name 1) (.name 0)) := by
  refine ⟨(EqE.pair_iff _ _ _ _).mpr ⟨project 0, project 1⟩, ?_⟩
  intro h
  have bad := (EqE.name_iff 0 1).mp ((EqE.pair_iff _ _ _ _).mp h).1
  cases bad

theorem partial_decryption_order_retained :
    EqE (.binary .partialDecrypt (projection 0) (projection 1))
      (.binary .partialDecrypt (.name 0) (.name 1)) ∧
    ¬ EqE (Term.binary .partialDecrypt (.name 0) (.name 1) : Term Nat)
      (.binary .partialDecrypt (.name 1) (.name 0)) := by
  refine ⟨(EqE.partialDecrypt_iff _ _ _ _).mpr ⟨project 0, project 1⟩, ?_⟩
  intro h
  have bad := (EqE.name_iff 0 1).mp ((EqE.partialDecrypt_iff _ _ _ _).mp h).1
  cases bad

theorem passive_heads_separated :
    ¬ EqE cipher (.spk (projection 0) (projection 1) (projection 2) (projection 3)) :=
  penc_not_eqE_spk _ _ _ _ _ _ _

abbrev normalCipher : Term Nat := .ternary .penc (.name 0) (.name 1) (.name 2)

private theorem normal_cipher_irreducible : Irreducible normalCipher := by
  intro t h
  rcases h.penc_cases with ⟨k, hk, _⟩ | ⟨r, hr, _⟩ | ⟨m, hm, _⟩
  · exact name_irreducible 0 k hk
  · exact name_irreducible 1 r hr
  · exact name_irreducible 2 m hm

theorem normal_cipher_shape : ∃ k r m, normalCipher = .ternary .penc k r m ∧
    EqE (projection 0) k ∧ EqE (projection 1) r ∧ EqE (projection 2) m :=
  (EqE.ternary .penc (project 0) (project 1) (project 2)).penc_irreducible_shape normal_cipher_irreducible

abbrev projectedCipher : Term Nat := .unary .fst (.binary .pair normalCipher (.const .bottom))

theorem irreducibility_required_for_literal_shape : EqE normalCipher projectedCipher ∧
    ¬ (∃ k r m, projectedCipher = .ternary .penc k r m) ∧ ¬ Irreducible projectedCipher := by
  have hs := (RootStep.fst normalCipher (.const .bottom)).to_modulo
  refine ⟨hs.sound.symm, ?_, fun h => h normalCipher hs⟩
  rintro ⟨k, r, m, he⟩
  cases he

/-- Destructor heads can disappear under full E; passive-head results are scoped. -/
theorem universal_head_preservation_refuted (n : Nat) :
    let t : Term Nat := .binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.name 1) (.name n))
    EqE t (.name n) ∧ t.headTag ≠ (Term.name (V := Nat) n).headTag := by
  exact ⟨(RootStep.decrypt (.name 0) (.name 1) (.name n)).to_modulo.sound, by intro h; cases h⟩

end ExplainableCrypto.Helios.Symbolic.FullStructureSPOT
