import ExplainableCrypto.Helios.Symbolic.PublicKeyOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {policy : Finset Nat} {handles : Nat}

/-- The structural key-origin argument depends on pair origins, no successful
whole-minimum decryption, and a classified key-valued selector chain. Actual
frame instances must discharge all three premises. -/
theorem Frame.minimum_public_key_form_of_origins (φ : Frame policy handles)
    (restricted : Finset Nat) (root : Fin handles)
    (hpair : ∀ r : Recipe handles, MinimalRecipe restricted φ.value r →
      ∀ x y, EqE (φ.eval r) (.binary .pair x y) → PairRecipeOrigin r)
    (hdec : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .dec a b) →
      ∀ out, ¬ DecryptionMatch (φ.eval a) (φ.eval b) out)
    (hchain : ∀ v (r : Recipe handles), ProjectionChain v r →
      ∀ k, EqE (φ.eval r) (.unary .pk k) → r = .var root)
    (r : Recipe handles) (hm : MinimalRecipe restricted φ.value r) {k : Ground}
    (he : EqE (φ.eval r) (.unary .pk k)) : r = .var root ∨ ∃ a, r = .unary .pk a := by
  cases r with
  | name a =>
    obtain ⟨_, hshape, _⟩ := he.symm.pk_irreducible_shape (name_irreducible a)
    cases hshape
  | const c =>
    obtain ⟨_, hshape, _⟩ := he.symm.pk_irreducible_shape (constant_irreducible c)
    cases hshape
  | var v => exact Or.inl (hchain v (.var v) .handle k he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨x, y, hpairValue, _⟩ := he.projection_pk_inversion hf
      have horigin := hpair a (hm.subterm (.unary f .hole)) x y hpairValue.sound
      obtain ⟨v, hc⟩ := hm.projection_chain_of_pair_origin hf horigin
      have hsyntax := hchain v _ hc k he
      cases hsyntax
    cases f with
    | pk => exact Or.inr ⟨a, rfl⟩
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | pair => exact False.elim (pk_not_eqE_pair _ _ _ he.symm)
    | partialDecrypt => exact False.elim (pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ he.symm)
    | mul => exact False.elim (mul_not_eqE_pk _ _ _ he)
    | add => exact False.elim (arithmetic_not_eqE_pk .add (Or.inl rfl) _ _ _ he)
    | compose => exact False.elim (arithmetic_not_eqE_pk .compose (Or.inr rfl) _ _ _ he)
    | dec =>
      obtain ⟨out, hd, _⟩ := he.decryption_pk_inversion
      exact False.elim (hdec a b hm out hd)
  | ternary f a b c =>
    cases f with
    | penc => exact False.elim (pk_not_eqE_penc _ _ _ _ he.symm)
    | checkspk => exact False.elim (proof_check_not_eqE_pk _ _ _ _ he)
  | spk a b c d => exact False.elim (pk_not_eqE_spk _ _ _ _ _ he.symm)

end ExplainableCrypto.Helios.Symbolic
