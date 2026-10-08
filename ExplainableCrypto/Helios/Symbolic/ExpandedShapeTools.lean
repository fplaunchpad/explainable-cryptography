import ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeyTransfer
import ExplainableCrypto.Helios.Symbolic.ExpandedPairOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Numeric results have none of the three constructor value classes used by
shape reflection. This is full-E exclusion, including nonliteral numerals. -/
theorem numeric_not_data_shapes (number : Nat) :
    ¬ (addNumeral (V := Empty) number).PairValue ∧
    ¬ (addNumeral (V := Empty) number).CiphertextValue ∧
    ¬ (addNumeral (V := Empty) number).PartialValue := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,b,he⟩
    have hh := (addNumeral_irreducible number).pair_head_of_eq he
    cases number <;> cases hh
  · rintro ⟨k,r,m,he⟩
    obtain ⟨_,_,_,hh,_⟩ := he.symm.penc_irreducible_shape (addNumeral_irreducible number)
    cases number <;> cases hh
  · rintro ⟨k,c,he⟩
    obtain ⟨_,_,hh,_⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (addNumeral_irreducible number)
    cases number <;> cases hh

/-- Actual expanded chains retain their pair/ciphertext/partial value classes.
Only the world whose values are classified needs numeric result values. -/
theorem expanded_projection_chain_shape_reflection (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn' : ExpandedResultsNumeric ns swap' left right rs)
    (v : Fin (ExpandedHandles n)) {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain v r) :
    (((expandedFrame ns swap' left right rs).eval r).PairValue → ((expandedFrame ns swap left right rs).eval r).PairValue) ∧
    (((expandedFrame ns swap' left right rs).eval r).CiphertextValue → ((expandedFrame ns swap left right rs).eval r).CiphertextValue) ∧
    (((expandedFrame ns swap' left right rs).eval r).PartialValue → ((expandedFrame ns swap left right rs).eval r).PartialValue) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨a,b,he⟩
    obtain ⟨i,k,hk,rfl⟩ := expanded_projection_pair_origin ns swap' left right rs hn' v hc he
    exact expanded_ballot_tail_pair_value ns swap left right rs i k hk
  · rintro ⟨k,s,m,he⟩
    obtain ⟨_,_,_,_,s',m',hv⟩ := expanded_projection_ciphertext_key_transfer ns swap' swap left right rs hn' v r hc he
    exact ⟨_,s',m',hv⟩
  · rintro ⟨k,c,he⟩
    obtain ⟨j,rfl⟩ := expanded_projection_partial_origin ns swap' left right rs hn' v hc he
    exact ⟨.name ns.secretKey,tallyCiphertext ns swap left right rs j,by simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial]; exact .refl _⟩

/-- Pair and partial values of source minima have constructor or borrowed
origins whose shapes persist without a smaller-observation premise. -/
theorem expanded_minimum_passive_values_forward (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r) :
    (((expandedFrame ns swap left right rs).eval r).PairValue → ((expandedFrame ns swap' left right rs).eval r).PairValue) ∧
    (((expandedFrame ns swap left right rs).eval r).PartialValue → ((expandedFrame ns swap' left right rs).eval r).PartialValue) := by
  constructor
  · rintro ⟨a,b,he⟩
    exact (expanded_minimum_pair_observation_form ns swap left right rs hn ns.restricted r hm he).pair_value ns swap' left right rs
  · rintro ⟨k,c,he⟩
    rcases expanded_minimum_partial_decryption_form ns swap left right rs hn ns.restricted r hm he with
      ⟨a,b,rfl⟩ | ⟨j,rfl⟩
    · exact ⟨_,_,.refl _⟩
    · exact ⟨.name ns.secretKey,tallyCiphertext ns swap' left right rs j,by simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial]; exact .refl _⟩

/-- An E6 match using the actual published partial binds the entire ciphertext.
Consequently its output equals that slot's actual result expression. E5 is a
separate alternative and is deliberately absent from this premise. -/
theorem expanded_trustee_E6_output (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (j : Fin (n+1)) (b : Ground) {key nonce message : Ground}
    (hk : ReducesModulo ((expandedFrame ns swap left right rs).eval (.var (expandedPartial j)))
      (.binary .partialDecrypt key (keyCiphertext key nonce message)))
    (hb : ReducesModulo b (keyCiphertext key nonce message)) :
    EqE message (tallyResult ns swap left right rs j) := by
  have hm : DecryptionMatch ((expandedFrame ns swap left right rs).eval (.var (expandedPartial j))) b message :=
    ⟨key,nonce,Or.inr hk,hb⟩
  simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial] at hk hm
  have hparts := (EqE.partialDecrypt_iff _ _ _ _).mp hk.sound
  exact hm.reduces.sound.symm.trans (.binary .dec (.refl _) (hb.sound.trans hparts.2.symm))

/-- Under reflected child shapes, any destination match of a source-minimum
 decryption must use a borrowed trustee E6 slot and return its result. This
 does not claim absence of that remaining match. -/
theorem expanded_minimum_decryption_match_result_of_reflection (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (ha : ((expandedFrame ns swap' left right rs).eval a).PartialValue → ((expandedFrame ns swap left right rs).eval a).PartialValue)
    (hb : ((expandedFrame ns swap' left right rs).eval b).CiphertextValue → ((expandedFrame ns swap left right rs).eval b).CiphertextValue)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (Term.binary .dec a b).nodeCount) {message : Ground}
    (hmatch : DecryptionMatch ((expandedFrame ns swap' left right rs).eval a)
      ((expandedFrame ns swap' left right rs).eval b) message) :
    ∃ j : Fin (n+1), a = .var (expandedPartial j) ∧ EqE message (tallyResult ns swap' left right rs j) := by
  obtain ⟨key,nonce,hk,hc⟩ := hmatch
  obtain ⟨k,s,p,hvalue⟩ := hb ⟨_,_,_,hc.sound⟩
  obtain ⟨kr,hpub,hsize,hkey,s',p',hvalue'⟩ := expanded_minimum_ciphertext_key_transfer ns swap swap' left right rs hn b
    (hm.subterm (.binaryRight .dec a .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega)) hvalue
  have hv : EqE ((expandedFrame ns swap left right rs).eval b)
      (.ternary .penc ((expandedFrame ns swap left right rs).eval kr) s p) :=
    hvalue.trans (.ternary .penc hkey.symm (.refl _) (.refl _))
  rcases hk with hk | hk
  · have hkey' := ((EqE.penc_iff _ _ _ _ _ _).mp (hvalue'.symm.trans hc.sound)).1
    have hprobe' := hkey'.trans (.unary .pk hk.sound.symm)
    have hprobe := (hobs kr (.unary .pk a) hpub hm.isPublic.1 (by simp only [Term.nodeCount]; omega)).mpr hprobe'
    obtain ⟨out,hout⟩ := DecryptionMatch.exists_of_values
      (hv.trans (.ternary .penc hprobe (.refl _) (.refl _))) (Or.inl (.refl _))
    exact False.elim (expanded_minimum_decryption_no_match ns swap left right rs hn ns.restricted a b hm out hout)
  · obtain ⟨ak,ac,hpart⟩ := ha ⟨_,_,hk.sound⟩
    rcases expanded_minimum_partial_decryption_form ns swap left right rs hn ns.restricted a
      (hm.subterm (.binaryLeft .dec .hole b)) hpart with ⟨u,v,rfl⟩ | ⟨j,rfl⟩
    · have hiff := partial_key_match_transfer _ _ u v b kr hm.isPublic hpub hsize hv hvalue' hobs
      obtain ⟨out,hout⟩ := hiff.mpr ⟨message,key,nonce,Or.inr hk,hc⟩
      exact False.elim (expanded_minimum_decryption_no_match ns swap left right rs hn ns.restricted _ _ hm out hout)
    · exact ⟨j,rfl,expanded_trustee_E6_output ns swap' left right rs j _ hk hc⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
