import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- With minimum children and the full name restriction, a successful decrypt
can only consume a raw public ciphertext constructor. Honest or mixed groups
would expose the election secret through a direct or minimum partial key. -/
theorem minimum_successful_decryption_ciphertext_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hs : ∃ m, DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) m) :
    ∃ key nonce p, b = .ternary .penc key nonce p := by
  classical
  obtain ⟨m,k,r,hk,hc⟩ := hs
  have hn : ¬ EqE (publicKey ns) (.unary .pk k) := by
    intro he
    have hsecret := (EqE.pk_iff _ _).mp he
    rcases hk with hd | hp
    · exact frame_secret_key_not_deducible ns swap left right a ha.isPublic
        (hd.sound.trans hsecret.symm)
    · obtain ⟨u,v,rfl⟩ := minimum_partial_decryption_form ns swap left right ns.restricted a ha hp.sound
      have hu := (EqE.partialDecrypt_iff _ _ _ _).mp hp.sound
      exact frame_secret_key_not_deducible ns swap left right u ha.isPublic.1
        (hu.1.trans hsecret.symm)
  obtain ⟨t,rfl,hkey,_⟩ := minimum_ciphertext_grouping ns swap left right ns.restricted b hb hc.sound
  by_cases hg : ∃ nr p, t.group = .constructed nr p
  · obtain ⟨nr,p,hg⟩ := hg
    exact ⟨t.keyRecipe,nr,p,minimum_constructed_group_recipe ns swap left right t hb hg
      (t.coherent_of_key_agreement ns swap left right _ hkey)⟩
  · exact False.elim (hn (t.key_agreement_public_key_of_nonconstructed ns _ hkey
      (fun nr p h => hg ⟨nr,p,h⟩)))

/-- Constructed decryption preserves its explicit plaintext. Direct E5 uses
one smaller public-key comparison. E6 uses minimum partial-key syntax and the
three existing probes, retaining the alternative where that term is an E5 key. -/
theorem minimum_key_constructed_decryption_transfer (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (a key nonce p : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hp : (Term.ternary .penc key nonce p).Public ns.restricted)
    (hobs : Frame.ObservationsBelow (frame ns swap left right) (frame ns swap' left right)
      (Term.binary .dec a (.ternary .penc key nonce p)).nodeCount)
    (hs : ∃ m, DecryptionMatch ((frame ns swap left right).eval a)
      ((frame ns swap left right).eval (.ternary .penc key nonce p)) m) :
    EqE ((frame ns swap' left right).eval (.binary .dec a (.ternary .penc key nonce p)))
      ((frame ns swap' left right).eval p) := by
  obtain ⟨m,k,r,hk,hc⟩ := hs
  rcases hk with hd | hpartial
  · have hkey := ((EqE.penc_iff _ _ _ _ _ _).mp hc.sound).1
    have h := hkey.trans (.unary .pk hd.sound.symm)
    have h' := (hobs key (.unary .pk a) hp.1 ha.isPublic
      (by simp only [Term.nodeCount]; have := nonce.nodeCount_pos; omega)).mp h
    exact (EqE.binary .dec (.refl _) (.ternary .penc h' (.refl _) (.refl _))).trans
      (RootStep.decrypt _ _ _).sound
  · obtain ⟨u,v,rfl⟩ := minimum_partial_decryption_form ns swap left right ns.restricted a ha hpartial.sound
    have hs : ∃ m, DecryptionMatch ((frame ns swap left right).eval (.binary .partialDecrypt u v))
        ((frame ns swap left right).eval (.ternary .penc key nonce p)) m :=
      ⟨m,k,r,Or.inr hpartial,hc⟩
    have ht := (partial_key_match_transfer (frame ns swap left right) (frame ns swap' left right)
      u v (.ternary .penc key nonce p) key ⟨ha.isPublic,hp⟩ hp.1
      (by simp only [Term.nodeCount]; omega) (.refl _) (.refl _) hobs).mp hs
    obtain ⟨out,hout⟩ := ht
    exact hout.reduces.sound.trans hout.explicit_plaintext.symm

/-- Successful and stuck decryption exhaust the final local operator. The
successful representative is the actual minimum plaintext child, preserving
its possibly different evaluated value in each voting world. -/
theorem minimum_children_decryption_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hforward : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right)
      (Term.binary .dec a b).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right)
      (Term.binary .dec a b).nodeCount) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.binary .dec a b) := by
  classical
  by_cases hs : ∃ m, DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) m
  · obtain ⟨key,nonce,p,rfl⟩ := minimum_successful_decryption_ciphertext_form ns swap left right a b ha hb hs
    obtain ⟨m,hm⟩ := hs
    exact ⟨p,hb.subterm (.ternaryThird .penc key nonce .hole),
      hm.reduces.sound.trans hm.explicit_plaintext.symm,
      minimum_key_constructed_decryption_transfer ns swap swap' left right a key nonce p ha hb.isPublic
        (observationsBelow_of_two_way_minima ns hf swap swap' left right _ hforward hreverse) ⟨m,hm⟩⟩
  · exact .of_minimal (minimum_stuck_decryption_of_children ns swap left right a b ha hb
      (fun m h => hs ⟨m,h⟩))

/-- Both orientations of the last remaining induction interface are now
derived from fresh historical frames and valid candidate substitutions. -/
theorem successful_decryption_transport (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) :
    Frame.SuccessfulDecryptionTransport (frame ns swap left right) (frame ns swap' left right) := by
  intro r _ hc _ hv hforward hreverse
  cases r with
  | name _ | var _ | const _ | unary _ _ | ternary _ _ _ _ | spk _ _ _ _ => cases hv
  | binary f a b =>
    cases f with
    | pair | mul | add | compose | partialDecrypt => cases hv
    | dec =>
      exact minimum_children_decryption_shared_of_two_way_minima ns hf swap swap' left right
        a b hc.1 hc.2 hforward hreverse

/-- Initial-frame static equivalence for all public equality tests and all
valid ground candidate representations. No bounded-observation or shared-minimum
premises remain. Final frames and process matching are separate obligations. -/
theorem initial_frame_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  staticEq_of_successful_decryption_transport ns hf left right
    (successful_decryption_transport ns hf false true left right)
    (successful_decryption_transport ns hf true false left right)

end ExplainableCrypto.Helios.Symbolic.Historical.General
