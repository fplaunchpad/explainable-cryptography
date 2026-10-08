import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedCompression
import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionClosure

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- Direct E5 needs one strictly smaller comparison, including when the public
secret recipe denotes a structured published partial. -/
theorem public_key_constructed_decryption_transfer (φ ψ : Frame restricted handles)
    (a key nonce p : Recipe handles) (ha : a.Public restricted)
    (hp : (Term.ternary .penc key nonce p).Public restricted)
    (hobs : φ.ObservationsBelow ψ (Term.binary .dec a (.ternary .penc key nonce p)).nodeCount)
    (he : EqE (φ.eval key) (.unary .pk (φ.eval a))) :
    EqE (ψ.eval (.binary .dec a (.ternary .penc key nonce p))) (ψ.eval p) := by
  have h := (hobs key (.unary .pk a) hp.1 ha
    (by simp only [Term.nodeCount]; have := nonce.nodeCount_pos; omega)).mp he
  exact (EqE.binary .dec (.refl _) (.ternary .penc h (.refl _) (.refl _))).trans
    (RootStep.decrypt _ _ _).sound

/-- A publicly constructed partial uses the generic key/binding probes. Their
E5 alternative remains available; no minimum hypothesis is needed here. -/
theorem public_partial_constructed_decryption_transfer (φ ψ : Frame restricted handles)
    (u v key nonce p : Recipe handles)
    (ha : (Term.binary .partialDecrypt u v).Public restricted)
    (hp : (Term.ternary .penc key nonce p).Public restricted)
    (hobs : φ.ObservationsBelow ψ
      (Term.binary .dec (.binary .partialDecrypt u v) (.ternary .penc key nonce p)).nodeCount)
    (hs : ∃ m, DecryptionMatch (φ.eval (.binary .partialDecrypt u v))
      (φ.eval (.ternary .penc key nonce p)) m) :
    EqE (ψ.eval (.binary .dec (.binary .partialDecrypt u v) (.ternary .penc key nonce p))) (ψ.eval p) := by
  have ht := (partial_key_match_transfer φ ψ u v (.ternary .penc key nonce p) key ⟨ha,hp⟩ hp.1
    (by simp only [Term.nodeCount]; omega) (.refl _) (.refl _) hobs).mp hs
  obtain ⟨out,hout⟩ := ht
  exact hout.reduces.sound.trans hout.explicit_plaintext.symm

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum ciphertext encrypted to a publicly denotable secret is a raw
constructor. Honest/mixed groups would expose the restricted election secret. -/
theorem expanded_minimum_ciphertext_public_secret_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (b secret : Recipe (ExpandedHandles n))
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hs : secret.Public ns.restricted) {nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval b)
      (.ternary .penc (.unary .pk ((expandedFrame ns swap left right rs).eval secret)) nonce message)) :
    ∃ key r p, b = .ternary .penc key r p := by
  classical
  obtain ⟨t,rfl,_,_,_,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn b hb ⟨_,_,_,he⟩
  have hk := t.key_agreement_of_valueWith ns _ expandedOld swap left right
    (expanded_honest_selector_value ns swap left right rs) he
  by_cases hg : ∃ r p, t.group = .constructed r p
  · obtain ⟨r,p,hg⟩ := hg
    exact ⟨t.keyRecipeWith expandedOld,r,p,
      expanded_minimum_constructed_group_recipe ns swap left right rs t hb hg ⟨_,_,_,he⟩⟩
  · have hk' := t.key_agreement_public_key_of_nonconstructed ns _ hk (fun r p h => hg ⟨r,p,h⟩)
    exact False.elim ((expanded_frame_opaque_protected ns swap left right rs hp).name_not_deducible secret hs
      (by simp [Names.restricted]) ((EqE.pk_iff _ _).mp hk').symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
