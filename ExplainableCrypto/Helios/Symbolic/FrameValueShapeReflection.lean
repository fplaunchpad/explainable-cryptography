import ExplainableCrypto.Helios.Symbolic.ValueShapeTransfer

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {handles : Nat}

/-- Shared structural induction for initial and published frames. Frame-specific
premises classify chains and pair origins, reflect ciphertext products, and
exclude data-shaped outputs of destination matches of source-minimum decryptions.
The last premise allows numeric success; it need not assert universal failure. -/
theorem minimum_value_shape_reflection_of_cases (φ ψ : Frame restricted handles)
    (hchain : ∀ v {r : Recipe handles}, ProjectionChain v r →
      ((ψ.eval r).PairValue → (φ.eval r).PairValue) ∧
      ((ψ.eval r).CiphertextValue → (φ.eval r).CiphertextValue) ∧
      ((ψ.eval r).PartialValue → (φ.eval r).PartialValue))
    (hpair : ∀ r : Recipe handles, MinimalRecipe restricted φ.value r →
      ∀ x y, EqE (φ.eval r) (.binary .pair x y) → PairRecipeOrigin r)
    (hmul : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .mul a b) →
      ((ψ.eval a).CiphertextValue → (φ.eval a).CiphertextValue) →
      ((ψ.eval b).CiphertextValue → (φ.eval b).CiphertextValue) →
      ObservationsBelow φ ψ (Term.binary .mul a b).nodeCount →
      (ψ.eval (.binary .mul a b)).CiphertextValue → (φ.eval (.binary .mul a b)).CiphertextValue)
    (hdec : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .dec a b) →
      ((ψ.eval a).PartialValue → (φ.eval a).PartialValue) →
      ((ψ.eval b).CiphertextValue → (φ.eval b).CiphertextValue) →
      ObservationsBelow φ ψ (Term.binary .dec a b).nodeCount →
      ∀ out, DecryptionMatch (ψ.eval a) (ψ.eval b) out →
        ¬ out.PairValue ∧ ¬ out.CiphertextValue ∧ ¬ out.PartialValue)
    (r : Recipe handles) :
    MinimalRecipe restricted φ.value r → ObservationsBelow φ ψ r.nodeCount →
    ((ψ.eval r).PairValue → (φ.eval r).PairValue) ∧
    ((ψ.eval r).CiphertextValue → (φ.eval r).CiphertextValue) ∧
    ((ψ.eval r).PartialValue → (φ.eval r).PartialValue) := by
  induction r with
  | name name =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b, he⟩
      obtain ⟨_, _, h, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inl rfl) (name_irreducible name)
      cases h
    · rintro ⟨k, r, m, he⟩
      obtain ⟨_, _, _, h, _⟩ := he.symm.penc_irreducible_shape (name_irreducible name)
      cases h
    · rintro ⟨a, b, he⟩
      obtain ⟨_, _, h, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (name_irreducible name)
      cases h
  | const c =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b, he⟩
      obtain ⟨_, _, h, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inl rfl) (constant_irreducible c)
      cases h
    · rintro ⟨k, r, m, he⟩
      obtain ⟨_, _, _, h, _⟩ := he.symm.penc_irreducible_shape (constant_irreducible c)
      cases h
    · rintro ⟨a, b, he⟩
      obtain ⟨_, _, h, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (constant_irreducible c)
      cases h
  | var v =>
    intro _ _
    exact hchain v .handle
  | unary f a ih =>
    intro hm hobs
    have ha := ih (hm.subterm (.unary f .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega))
    have project (hf : f = .fst ∨ f = .snd) :
        ((ψ.eval (.unary f a)).PairValue → (φ.eval (.unary f a)).PairValue) ∧
        ((ψ.eval (.unary f a)).CiphertextValue → (φ.eval (.unary f a)).CiphertextValue) ∧
        ((ψ.eval (.unary f a)).PartialValue → (φ.eval (.unary f a)).PartialValue) := by
      have chain {x y : Ground} (hp : EqE (ψ.eval a) (.binary .pair x y)) :
          ∃ v, ProjectionChain v (.unary f a) := by
        obtain ⟨u, v, huv⟩ := ha.1 ⟨x, y, hp⟩
        exact hm.projection_chain_of_pair_origin hf
          (hpair a (hm.subterm (.unary f .hole)) u v huv)
      refine ⟨?_, ?_, ?_⟩
      · intro h
        obtain ⟨x, y, he⟩ := h
        obtain ⟨u, v, hp, _⟩ := he.projection_pair_inversion hf
        obtain ⟨v, hc⟩ := chain hp.sound
        exact (hchain v hc).1 ⟨x, y, he⟩
      · intro h
        obtain ⟨k, r, m, he⟩ := h
        obtain ⟨u, v, hp, _⟩ := he.projection_penc_inversion hf
        obtain ⟨v, hc⟩ := chain hp.sound
        exact (hchain v hc).2.1 ⟨k, r, m, he⟩
      · intro h
        obtain ⟨k, c, he⟩ := h
        obtain ⟨u, v, hp, _⟩ := he.projection_partialDecrypt_inversion hf
        obtain ⟨v, hc⟩ := chain hp.sound
        exact (hchain v hc).2.2 ⟨k, c, he⟩
    cases f with
    | fst => exact project (Or.inl rfl)
    | snd => exact project (Or.inr rfl)
    | pk =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y, he⟩; exact False.elim (pk_not_eqE_pair _ x y he)
      · rintro ⟨k, r, m, he⟩; exact False.elim (pk_not_eqE_penc _ k r m he)
      · rintro ⟨k, c, he⟩; exact False.elim (pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ k c he)
  | binary f a b iha ihb =>
    intro hm hobs
    have ha := iha (hm.subterm (.binaryLeft f .hole b)) (hobs.mono (by simp only [Term.nodeCount]; omega))
    have hb := ihb (hm.subterm (.binaryRight f a .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega))
    cases f with
    | pair =>
      refine ⟨fun _ => ⟨_, _, .refl _⟩, ?_, ?_⟩
      · rintro ⟨k, r, m, he⟩; exact False.elim (penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ he.symm)
      · rintro ⟨k, c, he⟩
        have h := ((EqE.passive_binary_iff .pair .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _).mp he).1
        cases h
    | partialDecrypt =>
      refine ⟨?_, ?_, fun _ => ⟨_, _, .refl _⟩⟩
      · rintro ⟨x, y, he⟩
        have h := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp he).1
        cases h
      · rintro ⟨k, r, m, he⟩; exact False.elim (penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he.symm)
    | mul =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y, he⟩; exact False.elim (mul_not_eqE_passive_binary _ _ x y .pair (Or.inl rfl) he)
      · exact hmul a b hm ha.2.1 hb.2.1 hobs
      · rintro ⟨k, c, he⟩; exact False.elim (mul_not_eqE_passive_binary _ _ k c .partialDecrypt (Or.inr rfl) he)
    | add =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y, he⟩; exact False.elim (arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ x y he)
      · rintro ⟨k, r, m, he⟩; exact False.elim (arithmetic_not_eqE_penc .add (Or.inl rfl) _ _ k r m he)
      · rintro ⟨k, c, he⟩; exact False.elim (arithmetic_not_eqE_passive_binary .add .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ k c he)
    | compose =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y, he⟩; exact False.elim (arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ x y he)
      · rintro ⟨k, r, m, he⟩; exact False.elim (arithmetic_not_eqE_penc .compose (Or.inr rfl) _ _ k r m he)
      · rintro ⟨k, c, he⟩; exact False.elim (arithmetic_not_eqE_passive_binary .compose .partialDecrypt (Or.inr rfl) (Or.inr rfl) _ _ k c he)
    | dec =>
      have hn := hdec a b hm ha.2.2 hb.2.1 hobs
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y, he⟩
        obtain ⟨out, hmatch, hout⟩ := he.decryption_pair_inversion
        exact False.elim ((hn out hmatch).1 ⟨x,y,hout⟩)
      · rintro ⟨k, r, m, he⟩
        obtain ⟨out, hmatch, hout⟩ := he.decryption_penc_inversion
        exact False.elim ((hn out hmatch).2.1 ⟨k,r,m,hout⟩)
      · rintro ⟨k, c, he⟩
        obtain ⟨out, hmatch, hout⟩ := he.decryption_partialDecrypt_inversion
        exact False.elim ((hn out hmatch).2.2 ⟨k,c,hout⟩)
  | ternary f a b c _ _ _ =>
    intro _ _
    cases f with
    | penc =>
      refine ⟨?_, fun _ => ⟨_, _, _, .refl _⟩, ?_⟩
      · rintro ⟨x, y, he⟩; exact False.elim (penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ x y he)
      · rintro ⟨k, c, he⟩; exact False.elim (penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ k c he)
    | checkspk =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y, he⟩; exact False.elim (proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ x y he)
      · rintro ⟨k, r, m, he⟩; exact False.elim (proof_check_not_eqE_penc _ _ _ k r m he)
      · rintro ⟨k, c, he⟩; exact False.elim (proof_check_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ k c he)
  | spk a b c d _ _ _ _ =>
    intro _ _
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, y, he⟩; exact False.elim (spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ x y he)
    · rintro ⟨k, r, m, he⟩; exact False.elim (penc_not_eqE_spk k r m _ _ _ _ he.symm)
    · rintro ⟨k, c, he⟩; exact False.elim (spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ k c he)

end ExplainableCrypto.Helios.Symbolic.Frame
