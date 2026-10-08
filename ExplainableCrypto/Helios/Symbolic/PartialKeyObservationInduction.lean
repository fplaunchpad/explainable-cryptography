import ExplainableCrypto.Helios.Symbolic.DecryptionProbes

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- Three public equality probes detect both E5 and E6 for an explicit partial
key and a ciphertext with a smaller public key recipe. -/
theorem partial_key_match_transfer (φ ψ : Frame restricted handles)
    (a binding b key : Recipe handles)
    (hp : (Term.binary .dec (.binary .partialDecrypt a binding) b).Public restricted)
    (hkey : key.Public restricted) (hsize : key.nodeCount < b.nodeCount)
    {nonce p nonce' p' : Ground}
    (hb : EqE (φ.eval b) (.ternary .penc (φ.eval key) nonce p))
    (hb' : EqE (ψ.eval b) (.ternary .penc (ψ.eval key) nonce' p'))
    (hobs : φ.ObservationsBelow ψ
      ((Term.binary .dec (.binary .partialDecrypt a binding) b).nodeCount)) :
    (∃ m, DecryptionMatch (φ.eval (.binary .partialDecrypt a binding)) (φ.eval b) m) ↔
      ∃ m, DecryptionMatch (ψ.eval (.binary .partialDecrypt a binding)) (ψ.eval b) m := by
  have hd := hobs key (.unary .pk (.binary .partialDecrypt a binding)) hkey hp.1 (by
    simp only [Term.nodeCount]; omega)
  have hk := hobs key (.unary .pk a) hkey hp.1.1 (by
    simp only [Term.nodeCount]; omega)
  have hc := hobs binding b hp.1.2 hp.2 (by
    have := a.nodeCount_pos
    simp only [Term.nodeCount]; omega)
  exact (DecryptionMatch.partial_key_iff _ _ _ _ _ _ hb).trans
    ((or_congr hd (and_congr hk hc)).trans (DecryptionMatch.partial_key_iff _ _ _ _ _ _ hb').symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Coherence supplies ciphertext values in both worlds. Only source coherence
is assumed; the same small observations derive destination coherence. -/
theorem assembly_partial_key_match_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a binding : Recipe 3) (t : CiphertextAssembly n)
    (hp : (Term.binary .dec (.binary .partialDecrypt a binding) t.recipe).Public ns.restricted)
    (hc : t.Coherent (frame ns false left right))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      ((Term.binary .dec (.binary .partialDecrypt a binding) t.recipe).nodeCount)) :
    (∃ m, DecryptionMatch ((frame ns false left right).eval (.binary .partialDecrypt a binding))
      ((frame ns false left right).eval t.recipe) m) ↔
    ∃ m, DecryptionMatch ((frame ns true left right).eval (.binary .partialDecrypt a binding))
      ((frame ns true left right).eval t.recipe) m := by
  have hc' := (t.coherent_transfer _ _ hp.2 (hobs.mono (by simp only [Term.nodeCount]; omega))).mp hc
  have hv := t.grouped_value ns false left right _ (t.key_agreement_of_coherent ns false left right hc)
  have hv' := t.grouped_value ns true left right _ (t.key_agreement_of_coherent ns true left right hc')
  exact partial_key_match_transfer _ _ a binding t.recipe t.keyRecipe hp
    (t.keyRecipe_public hp.2) t.keyRecipe_smaller hv hv' hobs

/-- A minimum partial-key decryption of a ciphertext-valued recipe stays stuck.
Exact ciphertext assembly syntax and destination coherence are derived. -/
theorem minimum_partial_key_decryption_failure (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec a b))
    {k c key nonce p : Ground}
    (ha : EqE ((frame ns false left right).eval a) (.binary .partialDecrypt k c))
    (hb : EqE ((frame ns false left right).eval b) (.ternary .penc key nonce p))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      ((Term.binary .dec a b).nodeCount)) :
    ∀ m, ¬ DecryptionMatch ((frame ns true left right).eval a) ((frame ns true left right).eval b) m := by
  obtain ⟨u, v, rfl⟩ := minimum_partial_decryption_form ns false left right ns.restricted a
    (hm.subterm (.binaryLeft .dec .hole b)) ha
  obtain ⟨t, rfl, ht, _⟩ := minimum_ciphertext_grouping ns false left right ns.restricted b
    (hm.subterm (.binaryRight .dec (.binary .partialDecrypt u v) .hole)) hb
  have hiff := assembly_partial_key_match_swap ns left right u v t hm.isPublic
    (t.coherent_of_key_agreement ns _ left right key ht) hobs
  rintro m hmatch
  obtain ⟨m', hm'⟩ := hiff.mpr ⟨m, hmatch⟩
  exact minimum_decryption_no_match ns false left right ns.restricted _ _ hm m' hm'

/-- A two-sided equality branch for minima whose key arguments have partial
values and ciphertext arguments have ciphertext values in the source frame.
Destination failure follows from smaller probes, not destination minimality. -/
theorem minimum_partial_key_decryption_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b c d : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec a b))
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec c d))
    {ak ac bk br bp ck cc dk dr dp : Ground}
    (ha : EqE ((frame ns false left right).eval a) (.binary .partialDecrypt ak ac))
    (hb : EqE ((frame ns false left right).eval b) (.ternary .penc bk br bp))
    (hc : EqE ((frame ns false left right).eval c) (.binary .partialDecrypt ck cc))
    (hd : EqE ((frame ns false left right).eval d) (.ternary .penc dk dr dp))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      ((Term.binary .dec a b).nodeCount + (Term.binary .dec c d).nodeCount)) :
    EqE ((frame ns false left right).eval (.binary .dec a b)) ((frame ns false left right).eval (.binary .dec c d)) ↔
      EqE ((frame ns true left right).eval (.binary .dec a b)) ((frame ns true left right).eval (.binary .dec c d)) := by
  have hnr := minimum_decryption_no_match ns false left right ns.restricted a b hr
  have hns := minimum_decryption_no_match ns false left right ns.restricted c d hs
  have hnr' := minimum_partial_key_decryption_failure ns left right a b hr ha hb
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hns' := minimum_partial_key_decryption_failure ns left right c d hs hc hd
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have harg := hobs a c hr.isPublic.1 hs.isPublic.1 (by simp only [Term.nodeCount]; omega)
  have hciph := hobs b d hr.isPublic.2 hs.isPublic.2 (by simp only [Term.nodeCount]; omega)
  exact (EqE.decryption_iff_of_no_match _ _ _ _ hnr hns).trans
    ((and_congr harg hciph).trans (EqE.decryption_iff_of_no_match _ _ _ _ hnr' hns').symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
