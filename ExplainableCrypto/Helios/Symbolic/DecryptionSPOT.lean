import ExplainableCrypto.Helios.Symbolic.DecryptionLocalConfluence
import ExplainableCrypto.Helios.Symbolic.AtomIrreducibility

namespace ExplainableCrypto.Helios.Symbolic.DecryptionSPOT

abbrev key : Term Nat := .unary .fst (.binary .pair (.name 0) (.const .bottom))
abbrev nonce : Term Nat := .unary .snd (.binary .pair (.const .bottom) (.name 1))
abbrev message : Term Nat := .unary .fst (.binary .pair (.name 2) (.name 3))
abbrev cipher : Term Nat := keyCiphertext key nonce message
abbrev source : Term Nat := .binary .dec (.binary .partialDecrypt key cipher) cipher
abbrev keyChangedCipher : Term Nat := keyCiphertext (.name 0) nonce message
abbrev nonceChangedCipher : Term Nat := keyCiphertext key (.name 1) message
abbrev messageChangedCipher : Term Nat := keyCiphertext key nonce (.name 2)
abbrev fieldChanges : List (Term Nat) := [keyChangedCipher, nonceChangedCipher, messageChangedCipher]

theorem key_step : ModuloStep key (.name 0) := (RootStep.fst (.name 0) (.const .bottom)).to_modulo
theorem nonce_step : ModuloStep nonce (.name 1) := (RootStep.snd (.const .bottom) (.name 1)).to_modulo
theorem message_step : ModuloStep message (.name 2) := (RootStep.fst (.name 2) (.name 3)).to_modulo

theorem each_ciphertext_field_changes : ∀ c ∈ fieldChanges, ModuloStep cipher c := by
  intro c hc
  simp only [fieldChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact key_step.context (.ternaryFirst .penc (.unary .pk .hole) nonce message)
  · exact nonce_step.context (.ternarySecond .penc (.unary .pk key) .hole message)
  · exact message_step.context (.ternaryThird .penc (.unary .pk key) nonce .hole)

/-- All three field changes in either E6 ciphertext copy have actual first steps
and joins with the root branch. The list contains distinct explicit targets. -/
theorem both_e6_ciphertext_copies_join : ModuloStep source message ∧
    ∀ c ∈ fieldChanges,
      ModuloStep source (.binary .dec (.binary .partialDecrypt key c) cipher) ∧
      ModuloStep source (.binary .dec (.binary .partialDecrypt key cipher) c) ∧
      JoinModulo message (.binary .dec (.binary .partialDecrypt key c) cipher) ∧
      JoinModulo message (.binary .dec (.binary .partialDecrypt key cipher) c) := by
  refine ⟨(RootStep.partial_decrypt key nonce message).to_modulo, ?_⟩
  intro c hc
  have h := each_ciphertext_field_changes c hc
  have hl := h.context (.binaryRight .partialDecrypt key .hole)
  exact ⟨hl.context (.binaryLeft .dec .hole cipher), h.context (.binaryRight .dec
    (.binary .partialDecrypt key cipher) .hole), partial_decrypt_left_step_joined key nonce message hl,
    partial_decrypt_right_step_joined key nonce message h⟩

/-- The explicit E6 key is a seventh independent location for a component change. -/
theorem explicit_e6_key_joins :
    ModuloStep source (.binary .dec (.binary .partialDecrypt (.name 0) cipher) cipher) ∧
    JoinModulo message (.binary .dec (.binary .partialDecrypt (.name 0) cipher) cipher) := by
  have h := key_step.context (.binaryLeft .partialDecrypt .hole cipher)
  exact ⟨h.context (.binaryLeft .dec .hole cipher), partial_decrypt_left_step_joined key nonce message h⟩

/-- E5's ciphertext argument covers all three fields with the expected root plaintext. -/
theorem e5_ciphertext_fields_join :
    ModuloStep (.binary .dec key cipher) message ∧
    ∀ c ∈ fieldChanges, ModuloStep (.binary .dec key cipher) (.binary .dec key c) ∧
      JoinModulo message (.binary .dec key c) := by
  refine ⟨(RootStep.decrypt key nonce message).to_modulo, ?_⟩
  intro c hc
  have h := each_ciphertext_field_changes c hc
  exact ⟨h.context (.binaryRight .dec key .hole), decrypt_ciphertext_step_joined key nonce message h⟩

abbrev rightKeyChanged : Term Nat := .binary .dec (.binary .partialDecrypt key cipher) keyChangedCipher
abbrev twoKeysChanged : Term Nat := .binary .dec (.binary .partialDecrypt (.name 0) cipher) keyChangedCipher
abbrev allKeysChanged : Term Nat := .binary .dec
  (.binary .partialDecrypt (.name 0) keyChangedCipher) keyChangedCipher

/-- Two updated key occurrences are insufficient; the third copy matters. -/
theorem all_three_keys_required :
    (rootReduce rightKeyChanged).isNone = true ∧ (rootReduce twoKeysChanged).isNone = true ∧
    (rootReduce allKeysChanged).map Subtype.val = some message := by decide

/-- Independent fixed endpoint: the last two key copies synchronize, E6 returns
the original projected plaintext, and that projection returns name 2. -/
theorem right_key_routes_expected : ReducesModulo rightKeyChanged (.name 2) ∧
    ModuloStep message (.name 2) := by
  have h₁ : ModuloStep rightKeyChanged twoKeysChanged := key_step.context
    (.binaryLeft .dec (.binaryLeft .partialDecrypt .hole cipher) keyChangedCipher)
  have h₂ : ModuloStep twoKeysChanged allKeysChanged := key_step.context
    (.binaryLeft .dec (.binaryRight .partialDecrypt (.name 0)
      (.ternaryFirst .penc (.unary .pk .hole) nonce message)) keyChangedCipher)
  exact ⟨.head h₁ (.head h₂ (.head (RootStep.partial_decrypt (.name 0) nonce message).to_modulo
    (.single message_step))), message_step⟩

/-- A changed plaintext copy synchronizes to the updated plaintext, not a constant result. -/
theorem plaintext_copy_routes_expected :
    ReducesModulo (.binary .dec (.binary .partialDecrypt key cipher) messageChangedCipher) (.name 2) ∧
    (rootReduce (.binary .dec (.binary .partialDecrypt key cipher) messageChangedCipher)).isNone = true := by
  have h := message_step.context (.binaryLeft .dec (.binaryRight .partialDecrypt key
    (.ternaryThird .penc (.unary .pk key) nonce .hole)) messageChangedCipher)
  exact ⟨.head h (.single (RootStep.partial_decrypt key nonce (.name 2)).to_modulo), by decide⟩

/-- Preserve the gate's smallest mismatched-ciphertext counterexample. -/
theorem distinct_ciphertext_copies_no_match :
    (rootReduce (Term.binary .dec
      (.binary .partialDecrypt (.name 0) (keyCiphertext (.name 0) (.name 1) (.name 0)))
      (keyCiphertext (.name 0) (.name 1) (.name 1)) : Term Nat)).isNone = true := by decide

/-- Instantiate local confluence on E6 with three independently reducible parameters. -/
theorem e6_locally_confluent_nonvacuous : LocallyConfluentAt source ∧
    ModuloStep source message ∧ ModuloStep source rightKeyChanged ∧ message ≠ rightKeyChanged := by
  have hk : LocallyConfluentAt key := locally_confluent_at_unary .fst _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (name_irreducible 0).locally_confluent_at (constant_irreducible .bottom).locally_confluent_at)
  have hr : LocallyConfluentAt nonce := locally_confluent_at_unary .snd _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (constant_irreducible .bottom).locally_confluent_at (name_irreducible 1).locally_confluent_at)
  have hm : LocallyConfluentAt message := locally_confluent_at_unary .fst _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (name_irreducible 2).locally_confluent_at (name_irreducible 3).locally_confluent_at)
  have hc : LocallyConfluentAt cipher := locally_confluent_at_penc _ _ _
    (locally_confluent_at_unary .pk key hk) hr hm
  exact ⟨locally_confluent_at_decryption _ _
      (locally_confluent_at_passive_binary .partialDecrypt (Or.inr rfl) _ _ hk hc) hc,
    (RootStep.partial_decrypt key nonce message).to_modulo,
    (each_ciphertext_field_changes keyChangedCipher (by simp [fieldChanges])).context
      (.binaryRight .dec (.binary .partialDecrypt key cipher) .hole), by decide⟩

abbrev sumKey : Term Nat := .binary .add (.const .zero) (.const .one)
abbrev backgroundSource : Term Nat := .binary .dec (.const .one) (keyCiphertext sumKey nonce message)
abbrev backgroundChanged : Term Nat := .binary .dec (.const .one) (keyCiphertext sumKey (.name 1) message)

/-- E0-only key matching survives an independently chosen ciphertext nonce step. -/
theorem background_decryption_peak :
    (rootReduce backgroundSource).isNone = true ∧ ModuloStep backgroundSource message ∧
    ModuloStep backgroundSource backgroundChanged ∧ JoinModulo message backgroundChanged := by
  have hr : RootModuloStep backgroundSource message := ⟨_, _,
    .binary .dec (.refl _) (.ternary .penc (.unary .pk (.equation .zero_one)) (.refl _) (.refl _)),
    .decrypt (.const .one) nonce message, .refl _⟩
  have hi := nonce_step.context (.ternarySecond .penc (.unary .pk sumKey) .hole message)
  exact ⟨by decide, hr.to_modulo, hi.context (.binaryRight .dec (.const .one) .hole),
    decryption_root_right_joined hr hi⟩

theorem field_changes_distinct : fieldChanges.Nodup := by decide

/-- E5's explicit key change uses the general E0 root/internal theorem. -/
theorem explicit_e5_key_joins :
    ModuloStep (.binary .dec key cipher) (.binary .dec (.name 0) cipher) ∧
    JoinModulo message (.binary .dec (.name 0) cipher) ∧
    (rootReduce (.binary .dec (.name 0) cipher)).isNone = true := by
  have hr : RootModuloStep (.binary .dec key cipher) message :=
    ⟨_, _, .refl _, .decrypt key nonce message, .refl _⟩
  exact ⟨key_step.context (.binaryLeft .dec .hole cipher),
    decryption_root_left_joined hr key_step, by decide⟩

end ExplainableCrypto.Helios.Symbolic.DecryptionSPOT
