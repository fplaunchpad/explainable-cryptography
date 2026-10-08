import ExplainableCrypto.Helios.Symbolic.PartialDecryptionOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- Both ordered arguments remain strictly smaller public equality observations. -/
theorem partial_decryption_equality_transfer (φ ψ : Frame restricted handles) (a b a' b' : Recipe handles)
    (hp : (Term.binary .partialDecrypt a b).Public restricted)
    (hq : (Term.binary .partialDecrypt a' b').Public restricted)
    (hobs : φ.ObservationsBelow ψ
      ((Term.binary .partialDecrypt a b).nodeCount + (Term.binary .partialDecrypt a' b').nodeCount)) :
    EqE (φ.eval (.binary .partialDecrypt a b)) (φ.eval (.binary .partialDecrypt a' b')) ↔
      EqE (ψ.eval (.binary .partialDecrypt a b)) (ψ.eval (.binary .partialDecrypt a' b')) := by
  have ha := hobs a a' hp.1 hq.1 (by simp only [Term.nodeCount]; omega)
  have hb := hobs b b' hp.2 hq.2 (by simp only [Term.nodeCount]; omega)
  exact (EqE.partialDecrypt_iff _ _ _ _).trans ((and_congr ha hb).trans (EqE.partialDecrypt_iff _ _ _ _).symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Initial-frame minimum recipes with partial-decryption values have explicit
constructor syntax. No target normality or origin certificate is assumed. -/
theorem minimum_partial_decryption_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {k c : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.binary .partialDecrypt k c)) :
    ∃ a b, r = .binary .partialDecrypt a b := by
  cases r with
  | name a =>
    obtain ⟨_, _, hshape, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (name_irreducible a)
    cases hshape
  | const d =>
    obtain ⟨_, _, hshape, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (constant_irreducible d)
    cases hshape
  | var v => exact False.elim (frame_projection_not_partialDecrypt ns swap left right v .handle k c he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨x, y, hp, _⟩ := he.projection_partialDecrypt_inversion hf
      have horigin := minimum_pair_origin ns swap left right restricted a
        (hm.subterm (.unary f .hole)) hp.sound
      obtain ⟨v, hc⟩ := hm.projection_chain_of_pair_origin hf horigin
      exact frame_projection_not_partialDecrypt ns swap left right v hc k c he
    cases f with
    | pk => exact False.elim (pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ he)
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | partialDecrypt => exact ⟨a, b, rfl⟩
    | pair =>
      have hf := ((EqE.passive_binary_iff .pair .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _).mp he).1
      cases hf
    | mul => exact False.elim (mul_not_eqE_passive_binary _ _ _ _ .partialDecrypt (Or.inr rfl) he)
    | add =>
      exact False.elim
        (arithmetic_not_eqE_passive_binary .add .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _ he)
    | compose =>
      exact False.elim
        (arithmetic_not_eqE_passive_binary .compose .partialDecrypt (Or.inr rfl) (Or.inr rfl) _ _ _ _ he)
    | dec =>
      obtain ⟨out, hd, _⟩ := he.decryption_partialDecrypt_inversion
      exact False.elim (minimum_decryption_no_match ns swap left right restricted a b hm out hd)
  | ternary f a b d =>
    cases f with
    | penc => exact False.elim (penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he)
    | checkspk => exact False.elim (proof_check_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he)
  | spk a b d e => exact False.elim (spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ _ he)

/-- The initial-frame partial-decryption-valued branch uses first-world minima
and supplied values plus smaller public tests. It is not a theorem about final
frames that publish partial decryptions. -/
theorem minimum_partial_decryption_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {k c k' c' : Ground}
    (her : EqE ((frame ns false left right).eval r) (.binary .partialDecrypt k c))
    (hes : EqE ((frame ns false left right).eval s) (.binary .partialDecrypt k' c'))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨a, b, rfl⟩ := minimum_partial_decryption_form ns false left right ns.restricted r hr her
  obtain ⟨a', b', rfl⟩ := minimum_partial_decryption_form ns false left right ns.restricted s hs hes
  exact partial_decryption_equality_transfer _ _ a b a' b' hr.isPublic hs.isPublic hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
