import ExplainableCrypto.Helios.Symbolic.HistoricalProjectionChains
import ExplainableCrypto.Helios.Symbolic.ArithmeticSeparation
import ExplainableCrypto.Helios.Symbolic.ProofCheckSeparation

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- Literal pair construction or an actual fst/snd chain on one handle. -/
def PairRecipeOrigin (r : Term V) : Prop :=
  (∃ a b, r = .binary .pair a b) ∨ ∃ v, ProjectionChain v r

/-- Explicit constructors, selector chains and products. Semantic value premises
later restrict the selector leaves to honest ciphertext positions. -/
inductive CiphertextRecipeSyntax : Term V → Prop where
  | constructed (k r m : Term V) : CiphertextRecipeSyntax (.ternary .penc k r m)
  | selected {r : Term V} (v : V) (h : ProjectionChain v r) : CiphertextRecipeSyntax r
  | mul {a b : Term V} (ha : CiphertextRecipeSyntax a) (hb : CiphertextRecipeSyntax b) :
      CiphertextRecipeSyntax (.binary .mul a b)

/-- Every ciphertext E-value has a product certificate under the supplied key.
It also has the stated constructor/chain/product syntax. This is a proposition
to prove, not a general assumption about all frames. -/
def CiphertextCertificates (σ : V → Term W) (r : Term V) : Prop :=
  ∀ key nonce message, EqE (r.subst σ) (.ternary .penc key nonce message) →
    ∃ p s, CiphertextProduct σ key r p s ∧ CiphertextRecipeSyntax r

theorem CiphertextProduct.key_congr {σ : V → Term W} {key key' nonce : Term W} {r p : Term V}
    (h : CiphertextProduct σ key r p nonce) (he : EqE key key') :
    CiphertextProduct σ key' r p nonce := by
  induction h with
  | constructed k r m hk => exact .constructed k r m (hk.trans he)
  | constant r s c hc hs =>
    exact .constant r s c (hc.trans (.ternary .penc he (.refl _) (.refl _))) hs
  | mul _ _ ha hb => exact .mul ha hb

theorem EqE.decryption_pair_inversion {a b x y : Term V}
    (h : EqE (.binary .dec a b) (.binary .pair x y)) :
    ∃ p, DecryptionMatch a b p ∧ EqE p (.binary .pair x y) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.decryption_cases with ⟨_, _, _, _, ht⟩ | ⟨p, hp, hout⟩
  · obtain ⟨_, _, hp, _⟩ := hr.passive_binary_components (Or.inl rfl)
    cases (ht.symm.trans hp).head_eq
  · exact ⟨p, hp, hout.sound.trans hr.sound.symm⟩

theorem Irreducible.pair_head_of_eq {a x y : Term V} (ha : Irreducible a)
    (he : EqE a (.binary .pair x y)) : a.headTag = .binary .pair := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp he
  obtain ⟨_, _, hp, _⟩ := hr.passive_binary_components (Or.inl rfl)
  exact ((ha.reducesModulo hl).trans hp).head_eq

/-- Minimum projection cannot select from a literal pair recipe: that is a raw redex. -/
theorem MinimalRecipe.projection_chain_of_pair_origin {restricted : Finset Nat}
    {σ : V → Term W} {f : Unary} (hf : f = .fst ∨ f = .snd) {a : Term V}
    (hm : MinimalRecipe restricted σ (.unary f a)) (hp : PairRecipeOrigin a) :
    ∃ v, ProjectionChain v (.unary f a) := by
  rcases hp with ⟨x, y, rfl⟩ | ⟨v, hc⟩
  · rcases hf with rfl | rfl
    · exact False.elim (hm.raw_irreducible _ (RootStep.fst x y).to_rewrite)
    · exact False.elim (hm.raw_irreducible _ (RootStep.snd x y).to_rewrite)
  · exact ⟨v, .step f hf hc⟩

/-- Certificates for the smaller right recipe exclude any E5/E6 match of the whole minimum. -/
theorem MinimalRecipe.no_decryption_match_of_certificates {restricted : Finset Nat}
    {σ : V → Term W} {a b : Term V} (hm : MinimalRecipe restricted σ (.binary .dec a b))
    (hb : CiphertextCertificates σ b) (out : Term W) :
    ¬ DecryptionMatch (a.subst σ) (b.subst σ) out := by
  intro hd
  obtain ⟨k, s, hk, hc⟩ := hd
  obtain ⟨p, r, hp⟩ := hb _ _ _ hc.sound
  exact hp.1.no_minimum_decryption_match a hm out ⟨k, s, hk, hc⟩

end ExplainableCrypto.Helios.Symbolic
