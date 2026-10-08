import ExplainableCrypto.Helios.Symbolic.GeneralMinimumOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {policy : Finset Nat} {handles : Nat}

/-- Structural proof-value origins from pair origins and no successful whole-
minimum decryption. Each actual frame must discharge these two premises. -/
theorem Frame.minimum_proof_origin_of_origins (φ : Frame policy handles)
    (restricted : Finset Nat)
    (hpair : ∀ r : Recipe handles, MinimalRecipe restricted φ.value r →
      ∀ x y, EqE (φ.eval r) (.binary .pair x y) → PairRecipeOrigin r)
    (hdec : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .dec a b) →
      ∀ out, ¬ DecryptionMatch (φ.eval a) (φ.eval b) out)
    (recipe : Recipe handles) (hm : MinimalRecipe restricted φ.value recipe)
    {k s m c : Ground} (he : EqE (φ.eval recipe) (.spk k s m c)) :
    (∃ a b c d, recipe = .spk a b c d) ∨ ∃ v, ProjectionChain v recipe := by
  cases recipe with
  | name a =>
    obtain ⟨_, _, _, _, ht, _⟩ := he.symm.spk_irreducible_shape (name_irreducible a)
    cases ht
  | const d =>
    obtain ⟨_, _, _, _, ht, _⟩ := he.symm.spk_irreducible_shape (constant_irreducible d)
    cases ht
  | var v => exact Or.inr ⟨v, .handle⟩
  | unary f a =>
    have hp (hf : f = .fst ∨ f = .snd) : ∃ v, ProjectionChain v (.unary f a) := by
      obtain ⟨x, y, hx, _⟩ := he.projection_spk_inversion hf
      exact hm.projection_chain_of_pair_origin hf
        (hpair a (hm.subterm (.unary f .hole)) x y hx.sound)
    cases f with
    | pk => exact False.elim (pk_not_eqE_spk _ _ _ _ _ he)
    | fst => exact Or.inr (hp (Or.inl rfl))
    | snd => exact Or.inr (hp (Or.inr rfl))
  | binary f a b =>
    cases f with
    | pair => exact False.elim (spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ _ he.symm)
    | partialDecrypt =>
      exact False.elim (spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ _ he.symm)
    | mul => exact False.elim (mul_not_eqE_spk _ _ _ _ _ _ he)
    | add => exact False.elim (arithmetic_not_eqE_spk .add (Or.inl rfl) _ _ _ _ _ _ he)
    | compose => exact False.elim (arithmetic_not_eqE_spk .compose (Or.inr rfl) _ _ _ _ _ _ he)
    | dec =>
      obtain ⟨out, hd, _⟩ := he.decryption_spk_inversion
      exact False.elim (hdec a b hm out hd)
  | ternary f a b d =>
    cases f with
    | penc => exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ he)
    | checkspk => exact False.elim (proof_check_not_eqE_spk _ _ _ _ _ _ _ he)
  | spk a b c d => exact Or.inl ⟨a, b, c, d, rfl⟩

end ExplainableCrypto.Helios.Symbolic
