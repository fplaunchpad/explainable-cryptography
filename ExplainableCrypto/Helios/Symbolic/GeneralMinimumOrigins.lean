import ExplainableCrypto.Helios.Symbolic.GeneralProjectionOrigins
import ExplainableCrypto.Helios.Symbolic.MinimumOriginTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Selector-chain certificates are transported to the caller's semantic key. -/
theorem projection_chain_certificates (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) {r : Recipe 3} (hc : ∃ v, ProjectionChain v r) :
    CiphertextCertificates (frame ns swap left right).value r := by
  intro key nonce message he
  obtain ⟨v, hc⟩ := hc
  obtain ⟨i, j, _, rfl, hval⟩ := frame_projection_ciphertext_origin ns swap left right v hc he
  have hk := ((EqE.penc_iff _ _ _ _ _ _).mp hval).1
  obtain ⟨bit, _, hc⟩ := honest_projection_certificate ns swap left right i j
  exact ⟨_, _, hc.key_congr hk, .selected i.succ (.project i.succ j.val)⟩

private theorem minimum_projection_origins (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) {f : Unary}
    (hf : f = .fst ∨ f = .snd) (a : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.unary f a))
    (hp : ∀ x y, EqE ((frame ns swap left right).eval a) (.binary .pair x y) → PairRecipeOrigin a) :
    (∀ x y, EqE ((frame ns swap left right).eval (.unary f a)) (.binary .pair x y) →
      PairRecipeOrigin (.unary f a)) ∧
    CiphertextCertificates (frame ns swap left right).value (.unary f a) := by
  constructor
  · intro x y he
    obtain ⟨p, q, hpair, _⟩ := he.projection_pair_inversion hf
    exact Or.inr (hm.projection_chain_of_pair_origin hf (hp p q hpair.sound))
  · intro key nonce message he
    obtain ⟨p, q, hpair, _⟩ := he.projection_penc_inversion hf
    exact projection_chain_certificates ns swap left right
      (hm.projection_chain_of_pair_origin hf (hp p q hpair.sound)) key nonce message he

/-- Simultaneous induction discharges the historical ciphertext certificate.
Minimum publicness and the actual initial frame remain in the statement. -/
theorem minimum_pair_and_ciphertext_origins (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3) :
    MinimalRecipe restricted (frame ns swap left right).value r →
      (∀ x y, EqE ((frame ns swap left right).eval r) (.binary .pair x y) → PairRecipeOrigin r) ∧
      CiphertextCertificates (frame ns swap left right).value r := by
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
      exact False.elim (frame_handle_not_ciphertext ns swap left right v key nonce message he)
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
    | fst => exact minimum_projection_origins ns swap left right restricted (Or.inl rfl) a hm ha.1
    | snd => exact minimum_projection_origins ns swap left right restricted (Or.inr rfl) a hm ha.1
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
        exact ⟨c, b.subst (frame ns swap left right).value,
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

theorem minimum_pair_origin (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {x y : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.binary .pair x y)) : PairRecipeOrigin r :=
  (minimum_pair_and_ciphertext_origins ns swap left right restricted r hm).1 x y he

/-- The public corollary includes actual reconstruction, publicness, strict size,
and both supplied target component equations. No certificate is assumed. -/
theorem minimum_ciphertext_certificate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.ternary .penc key nonce message)) :
    ∃ p s, CiphertextProduct (frame ns swap left right).value key r p s ∧
      p.Public restricted ∧ p.nodeCount < r.nodeCount ∧ EqE s nonce ∧
      EqE ((frame ns swap left right).eval p) message := by
  obtain ⟨p, s, hp, _⟩ := (minimum_pair_and_ciphertext_origins ns swap left right restricted r hm).2
    key nonce message he
  have hvalues := (EqE.penc_iff _ _ _ _ _ _).mp (hp.sound.symm.trans he)
  exact ⟨p, s, hp, hp.plaintext_public hm.isPublic, hp.plaintext_smaller, hvalues.2.1, hvalues.2.2⟩

theorem minimum_ciphertext_syntax (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.ternary .penc key nonce message)) :
    CiphertextRecipeSyntax r := by
  obtain ⟨_, _, _, hs⟩ := (minimum_pair_and_ciphertext_origins ns swap left right restricted r hm).2
    key nonce message he
  exact hs

end ExplainableCrypto.Helios.Symbolic.Historical.General
