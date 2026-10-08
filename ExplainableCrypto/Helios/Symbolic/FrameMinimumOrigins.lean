import ExplainableCrypto.Helios.Symbolic.MinimumOriginTools

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {policy : Finset Nat} {handles : Nat}

private theorem minimum_projection_origins (φ : Frame policy handles)
    (hchains : ∀ r : Recipe handles, (∃ v, ProjectionChain v r) → CiphertextCertificates φ.value r)
    (restricted : Finset Nat) {f : Unary}
    (hf : f = .fst ∨ f = .snd) (a : Recipe handles)
    (hm : MinimalRecipe restricted φ.value (.unary f a))
    (hp : ∀ x y, EqE (φ.eval a) (.binary .pair x y) → PairRecipeOrigin a) :
    (∀ x y, EqE (φ.eval (.unary f a)) (.binary .pair x y) →
      PairRecipeOrigin (.unary f a)) ∧
    CiphertextCertificates φ.value (.unary f a) := by
  constructor
  · intro x y he
    obtain ⟨p, q, hpair, _⟩ := he.projection_pair_inversion hf
    exact Or.inr (hm.projection_chain_of_pair_origin hf (hp p q hpair.sound))
  · intro key nonce message he
    obtain ⟨p, q, hpair, _⟩ := he.projection_penc_inversion hf
    exact hchains _
      (hm.projection_chain_of_pair_origin hf (hp p q hpair.sound)) key nonce message he

/-- Reusable simultaneous origin induction. The handle-shape and projection
certificate premises are substantive and must be proved for the actual frame. -/
theorem minimum_pair_and_ciphertext_origins (φ : Frame policy handles)
    (hhandles : ∀ v key nonce message, ¬ EqE (φ.value v) (.ternary .penc key nonce message))
    (hchains : ∀ r : Recipe handles, (∃ v, ProjectionChain v r) → CiphertextCertificates φ.value r)
    (restricted : Finset Nat) (r : Recipe handles) :
    MinimalRecipe restricted φ.value r →
      (∀ x y, EqE (φ.eval r) (.binary .pair x y) → PairRecipeOrigin r) ∧
      CiphertextCertificates φ.value r := by
  induction r with
  | name a =>
    intro hm
    constructor
    · intro x y he
      cases (name_irreducible a).pair_head_of_eq he
    · intro key nonce message he
      obtain ⟨_, _, _, ht, _⟩ := he.symm.penc_irreducible_shape (name_irreducible a)
      cases ht
  | var v =>
    intro hm
    constructor
    · exact fun _ _ _ => Or.inr ⟨v, .handle⟩
    · intro key nonce message he
      exact False.elim (hhandles v key nonce message he)
  | const c =>
    intro hm
    constructor
    · intro x y he
      have hh := (constant_irreducible c).pair_head_of_eq he
      cases c <;> cases hh
    · intro key nonce message he
      obtain ⟨_, _, _, ht, _⟩ := he.symm.penc_irreducible_shape (constant_irreducible c)
      cases ht
  | unary f a ih =>
    intro hm
    have ha := ih (hm.subterm (.unary f .hole))
    cases f with
    | fst => exact minimum_projection_origins φ hchains restricted (Or.inl rfl) a hm ha.1
    | snd => exact minimum_projection_origins φ hchains restricted (Or.inr rfl) a hm ha.1
    | pk =>
      constructor
      · exact fun x y he => False.elim (pk_not_eqE_pair _ x y he)
      · exact fun key nonce message he => False.elim (pk_not_eqE_penc _ key nonce message he)
  | binary f a b iha ihb =>
    intro hm
    have ha := iha (hm.subterm (.binaryLeft f .hole b))
    have hb := ihb (hm.subterm (.binaryRight f a .hole))
    cases f with
    | pair =>
      constructor
      · exact fun _ _ _ => Or.inl ⟨a, b, rfl⟩
      · exact fun key nonce message he => False.elim
          (penc_not_eqE_passive_binary .pair (Or.inl rfl) key nonce message _ _ he.symm)
    | partialDecrypt =>
      constructor
      · intro x y he
        have hh := ((EqE.passive_binary_iff .partialDecrypt .pair
          (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp he).1
        cases hh
      · exact fun key nonce message he => False.elim
          (penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) key nonce message _ _ he.symm)
    | mul =>
      constructor
      · exact fun x y he => False.elim (mul_not_eqE_passive_binary _ _ x y .pair (Or.inl rfl) he)
      · intro key nonce message he
        obtain ⟨r, s, m, n, he₁, he₂, _, _⟩ := he.mul_penc_inversion
        obtain ⟨p, u, hp⟩ := ha.2 key r m he₁
        obtain ⟨q, v, hq⟩ := hb.2 key s n he₂
        exact ⟨.binary .add p q, .binary .compose u v, .mul hp.1 hq.1, .mul hp.2 hq.2⟩
    | add =>
      constructor
      · exact fun x y he => False.elim
          (arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ x y he)
      · exact fun key nonce message he => False.elim
          (arithmetic_not_eqE_penc .add (Or.inl rfl) _ _ key nonce message he)
    | compose =>
      constructor
      · exact fun x y he => False.elim
          (arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ x y he)
      · exact fun key nonce message he => False.elim
          (arithmetic_not_eqE_penc .compose (Or.inr rfl) _ _ key nonce message he)
    | dec =>
      have hn := hm.no_decryption_match_of_certificates hb.2
      constructor
      · intro x y he
        obtain ⟨out, hd, _⟩ := he.decryption_pair_inversion
        exact False.elim (hn out hd)
      · intro key nonce message he
        obtain ⟨out, hd, _⟩ := he.decryption_penc_inversion
        exact False.elim (hn out hd)
  | ternary f a b c iha ihb ihc =>
    intro hm
    cases f with
    | penc =>
      constructor
      · exact fun x y he => False.elim
          (penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ x y he)
      · intro key nonce message he
        exact ⟨c, b.subst φ.value,
          .constructed a b c ((EqE.penc_iff _ _ _ _ _ _).mp he).1, .constructed a b c⟩
    | checkspk =>
      constructor
      · exact fun x y he => False.elim
          (proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ x y he)
      · exact fun key nonce message he => False.elim
          (proof_check_not_eqE_penc _ _ _ key nonce message he)
  | spk a b c d iha ihb ihc ihd =>
    intro hm
    constructor
    · exact fun x y he => False.elim (spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ x y he)
    · exact fun key nonce message he => False.elim (penc_not_eqE_spk key nonce message _ _ _ _ he.symm)

end ExplainableCrypto.Helios.Symbolic.Frame
