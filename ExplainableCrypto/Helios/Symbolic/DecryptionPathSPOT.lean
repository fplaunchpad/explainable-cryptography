import ExplainableCrypto.Helios.Symbolic.MinimalDecryption
import ExplainableCrypto.Helios.Symbolic.ProjectionPaths
import ExplainableCrypto.Helios.Symbolic.HistoricalMinimalDecryption
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT

namespace ExplainableCrypto.Helios.Symbolic.DecryptionPathSPOT

abbrev reveal (t : Term Nat) : Term Nat := .unary .fst (.binary .pair t (.const .bottom))
abbrev target : Term Nat := .ternary .penc (.name 2) (.name 3) (.name 4)
abbrev enc : Term Nat := keyCiphertext (.name 0) (.name 1) (reveal target)
abbrev directSource : Term Nat := .binary .dec (reveal (.name 0)) (reveal enc)
abbrev partialSource : Term Nat := .binary .dec
  (reveal (.binary .partialDecrypt (reveal (.name 0)) (reveal enc))) (reveal (reveal enc))

private theorem revealed (t : Term Nat) : ReducesModulo (reveal t) t :=
  .single (RootStep.fst t (.const .bottom)).to_modulo

theorem delayed_direct_match :
    DecryptionMatch (reveal (.name 0)) (reveal enc) (reveal target) :=
  ⟨.name 0, .name 1, Or.inl (revealed _), revealed _⟩

theorem delayed_partial_match :
    DecryptionMatch (reveal (.binary .partialDecrypt (reveal (.name 0)) (reveal enc)))
      (reveal (reveal enc)) (reveal target) :=
  ⟨.name 0, .name 1,
    Or.inr ((revealed _).trans (ReducesModulo.binary .partialDecrypt (revealed _) (revealed _))),
    (revealed _).trans (revealed _)⟩

/-- Both rules expose a reducible plaintext and continue to the independently fixed ciphertext. -/
theorem delayed_paths_expected : ReducesModulo directSource target ∧
    ReducesModulo partialSource target :=
  ⟨delayed_direct_match.reduces.trans (revealed _),
    delayed_partial_match.reduces.trans (revealed _)⟩

theorem delayed_path_classification :
    (∃ p, DecryptionMatch (reveal (.name 0)) (reveal enc) p ∧ EqE p target) ∧
    (∃ p, DecryptionMatch (reveal (.binary .partialDecrypt (reveal (.name 0)) (reveal enc)))
      (reveal (reveal enc)) p ∧ EqE p target) :=
  ⟨delayed_paths_expected.1.sound.decryption_penc_inversion,
    delayed_paths_expected.2.sound.decryption_penc_inversion⟩

/-- The negative gate's missing-shape fixture has an actual full-E ciphertext result. -/
theorem initial_ciphertext_shape_not_required : EqE directSource target ∧
    ¬ (∃ k r m, reveal enc = .ternary .penc k r m) := by
  refine ⟨delayed_paths_expected.1.sound, ?_⟩
  rintro ⟨k, r, m, h⟩
  cases h

abbrev stuckCipher : Term Nat := .ternary .penc (.var 1) (.var 2) (.var 3)
abbrev stuck : Term Nat := .binary .dec (.var 0) stuckCipher

private theorem stuck_cipher_irreducible : Irreducible stuckCipher := by
  intro t ht
  rcases ht.penc_cases with ⟨k, hk, _⟩ | ⟨r, hr, _⟩ | ⟨m, hm, _⟩
  · exact var_irreducible 1 k hk
  · exact var_irreducible 2 r hr
  · exact var_irreducible 3 m hm

theorem stuck_irreducible : Irreducible stuck := by
  intro t ht
  rcases ht.rigid_binary_cases (by simp [AC]) with hroot | ⟨a, ha, _⟩ | ⟨b, hb, _⟩
  · rcases hroot.decryption_cases with ⟨k, r, m, _, hc, _⟩ | ⟨k, r, m, ha, _, _⟩
    · have hk := ((BaseEq.penc_iff _ _ _ _ _ _).mp hc).1
      cases hk.head_eq
    · cases ha.head_eq
  · exact var_irreducible 0 a ha
  · exact stuck_cipher_irreducible b hb

/-- A concrete six-node minimum proves that the head-preservation premise is inhabited. -/
theorem stuck_minimal : MinimalRecipe {9} (Term.var : Nat → Term Nat) stuck :=
  MinimalRecipe.of_irreducible_weight (by trivial) stuck_irreducible rfl

theorem stuck_normal_shape : ∃ a b, stuck = .binary .dec a b ∧
    EqE (.var 0 : Term Nat) a ∧ EqE stuckCipher b :=
  stuck_minimal.explicit_decryption_normal_shape _ _ _ _ stuck_irreducible (.refl _)

theorem stuck_normal_composition : BaseEq stuck (.binary .dec (.var 0) stuckCipher) :=
  stuck_minimal.explicit_decryption_normal_form _ _ _ _
    (var_irreducible 0) stuck_cipher_irreducible stuck_irreducible (.refl _) (.refl _) (.refl _)

theorem stuck_never_matches (m : Term Nat) : ¬ DecryptionMatch (.var 0) stuckCipher m :=
  stuck_minimal.no_explicit_decryption_match _ _ _ _ m

theorem expected_target_irreducible : Irreducible target := by
  intro t ht
  rcases ht.penc_cases with ⟨k, hk, _⟩ | ⟨r, hr, _⟩ | ⟨m, hm, _⟩
  · exact name_irreducible 2 k hk
  · exact name_irreducible 3 r hr
  · exact name_irreducible 4 m hm

/-- Without minimality, an explicit-ciphertext decrypt reaches a different normal head. -/
theorem matching_decrypt_not_minimal :
    ReducesModulo (.binary .dec (.name 0) enc) target ∧
      ¬ MinimalRecipe {9} (Term.var : Nat → Term Nat) (.binary .dec (.name 0) enc) := by
  have he : ReducesModulo (.binary .dec (.name 0) enc) target :=
    (ReducesModulo.single (RootStep.decrypt (.name 0) (.name 1) (reveal target)).to_modulo).trans
      (revealed _)
  refine ⟨he, ?_⟩
  intro hm
  exact hm.explicit_decryption_not_ciphertext _ _ _ _ _ _ _ he.sound

/-- A non-normal equivalent can still wrap a minimum decrypt in a projection. -/
theorem normal_target_premise_required :
    EqE stuck (reveal stuck) ∧
      ¬ (∃ a b, reveal stuck = .binary .dec a b) ∧
      ¬ Irreducible (reveal stuck) := by
  have hs := (RootStep.fst stuck (.const .bottom)).to_modulo
  refine ⟨hs.sound.symm, ?_, fun h => h stuck hs⟩
  rintro ⟨a, b, he⟩
  cases he

abbrev histNames := HistoricalFrameSPOT.names
abbrev histFrame := Historical.frame histNames false 0 1
abbrev histCipher : Ground := .ternary .penc (.unary .pk (.name 10)) (.name 20) (.const .one)
abbrev histArgument : Recipe 3 := .unary .fst (.var 1)
abbrev histDecrypt : Recipe 3 := .binary .dec (.name 10) histArgument

/-- Lemma 9 permits the literal secret-key name under its nonce-only policy.
This real decrypt succeeds but is nonminimum because the public bit is smaller. -/
theorem historical_projected_decrypt_not_minimal :
    histDecrypt.Public histNames.nonceNames ∧
      EqE (histFrame.eval histDecrypt) (.const .one) ∧
      ¬ MinimalRecipe histNames.nonceNames histFrame.value histDecrypt := by
  have hright : ReducesModulo (histFrame.eval histArgument) histCipher :=
    .single (RootStep.fst histCipher
      (Term.tuple ((Historical.ballotFields histNames 0 0).drop 1))).to_modulo
  have hm : DecryptionMatch (histFrame.eval (.name 10)) (histFrame.eval histArgument) (.const .one) :=
    ⟨.name 10, .name 20, Or.inl (.refl _), hright⟩
  refine ⟨?_, hm.reduces.sound, ?_⟩
  · change 10 ∉ histNames.nonceNames ∧ True
    decide
  · intro hmin
    exact Historical.minimum_honest_component_no_decryption_match histNames false 0 1
      (.name 10) histArgument hmin 0 0 hright.sound (.const .one) hm

end ExplainableCrypto.Helios.Symbolic.DecryptionPathSPOT
