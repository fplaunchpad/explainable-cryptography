import ExplainableCrypto.Helios.Symbolic.MinimalDecryption

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- A factor-origin certificate for a nonempty ciphertext product under a common
semantic key. The nonce index is a value, not a claimed public nonce recipe.
This grammar does not classify all ciphertext-valued recipes. -/
inductive CiphertextProduct (σ : V → Term W) (key : Term W) :
    Term V → Term V → Term W → Prop where
  | constructed (k r m : Term V) (hk : EqE (k.subst σ) key) :
      CiphertextProduct σ key (.ternary .penc k r m) m (r.subst σ)
  | constant (r : Term V) (nonce : Term W) (c : Constant)
      (he : EqE (r.subst σ) (.ternary .penc key nonce (.const c)))
      (hs : 1 < r.nodeCount) : CiphertextProduct σ key r (.const c) nonce
  | mul {a b p q r s} (ha : CiphertextProduct σ key a p r)
      (hb : CiphertextProduct σ key b q s) :
      CiphertextProduct σ key (.binary .mul a b) (.binary .add p q) (.binary .compose r s)

namespace CiphertextProduct
variable {σ : V → Term W} {key nonce : Term W} {r p : Term V}

/-- The certificate's message and nonce trees agree with full E, including multiplicity. -/
theorem sound (h : CiphertextProduct σ key r p nonce) :
    EqE (r.subst σ) (.ternary .penc key nonce (p.subst σ)) := by
  induction h with
  | constructed k r m hk => exact .ternary .penc hk (.refl _) (.refl _)
  | constant r nonce c he _ => exact he
  | mul _ _ ha hb =>
    exact (EqE.binary .mul ha hb).trans (RootStep.homomorphic _ _ _ _ _).sound

theorem plaintext_public (h : CiphertextProduct σ key r p nonce)
    {restricted : Finset Nat} (hr : r.Public restricted) : p.Public restricted := by
  induction h with
  | constructed => exact hr.2.2
  | constant => trivial
  | mul _ _ ha hb => exact ⟨ha hr.1, hb hr.2⟩

theorem plaintext_smaller (h : CiphertextProduct σ key r p nonce) :
    p.nodeCount < r.nodeCount := by
  induction h with
  | constructed => simp only [Term.nodeCount]; omega
  | constant _ _ _ _ hs => exact hs
  | mul _ _ ha hb => simp only [Term.nodeCount]; omega

/-- Successful decryption of any certified product contradicts minimum recipe size. -/
theorem no_minimum_decryption_match (h : CiphertextProduct σ key r p nonce)
    (a : Term V) {restricted : Finset Nat}
    (hm : MinimalRecipe restricted σ (.binary .dec a r)) (out : Term W) :
    ¬ DecryptionMatch (a.subst σ) (r.subst σ) out := by
  intro hd
  have hdec := hd.reduces.sound
  obtain ⟨k, n, _, hc⟩ := hd
  have hp : EqE (p.subst σ) out :=
    ((EqE.penc_iff _ _ _ _ _ _).mp (h.sound.symm.trans hc.sound)).2.2
  apply hm.no_smaller (h.plaintext_public hm.isPublic.2) (hdec.trans hp.symm)
  have hs := h.plaintext_smaller
  simp only [Term.nodeCount]
  omega

/-- Exact composition with independently supplied normal argument representatives. -/
theorem minimum_decryption_normal_form (h : CiphertextProduct σ key r p nonce)
    (a : Term V) {restricted : Finset Nat}
    (hm : MinimalRecipe restricted σ (.binary .dec a r))
    {a' b' t : Term W} (ha : Irreducible a') (hb : Irreducible b') (ht : Irreducible t)
    (hea : EqE (a.subst σ) a') (heb : EqE (r.subst σ) b')
    (he : EqE ((.binary .dec a r : Term V).subst σ) t) :
    BaseEq t (.binary .dec a' b') :=
  decryption_normal_form_of_no_match _ _ (h.no_minimum_decryption_match a hm) ha hb ht hea heb he

theorem minimum_decryption_normal_shape (h : CiphertextProduct σ key r p nonce)
    (a : Term V) {restricted : Finset Nat}
    (hm : MinimalRecipe restricted σ (.binary .dec a r))
    {t : Term W} (ht : Irreducible t)
    (he : EqE ((.binary .dec a r : Term V).subst σ) t) :
    ∃ a' b', t = .binary .dec a' b' ∧ EqE (a.subst σ) a' ∧ EqE (r.subst σ) b' :=
  decryption_normal_shape_of_no_match _ _ (h.no_minimum_decryption_match a hm) ht he

end CiphertextProduct
end ExplainableCrypto.Helios.Symbolic
