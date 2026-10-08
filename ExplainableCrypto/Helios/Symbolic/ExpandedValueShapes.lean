import ExplainableCrypto.Helios.Symbolic.ExpandedShapeTools
import ExplainableCrypto.Helios.Symbolic.FrameValueShapeReflection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Simultaneous reflection for actual expanded frames. Numeric results in both
assignments discharge the borrowed E6 output case; source minimum size and
observations below this recipe suffice. Destination minimum size is absent. -/
theorem expanded_minimum_value_shape_reflection (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (hn' : ExpandedResultsNumeric ns swap' left right rs) (r : Recipe (ExpandedHandles n)) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r →
    (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount →
    (((expandedFrame ns swap' left right rs).eval r).PairValue → ((expandedFrame ns swap left right rs).eval r).PairValue) ∧
    (((expandedFrame ns swap' left right rs).eval r).CiphertextValue → ((expandedFrame ns swap left right rs).eval r).CiphertextValue) ∧
    (((expandedFrame ns swap' left right rs).eval r).PartialValue → ((expandedFrame ns swap left right rs).eval r).PartialValue) := by
  apply Frame.minimum_value_shape_reflection_of_cases (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
    (fun v _ hc => expanded_projection_chain_shape_reflection ns swap swap' left right rs hn' v hc)
    (fun r hm _ _ he => expanded_minimum_pair_origin ns swap left right rs hn ns.restricted r hm he)
  · intro a b hm ha hb hobs
    rintro ⟨key,nonce,message,he⟩
    obtain ⟨ra,rb,ma,mb,hea,heb,_,_⟩ := he.mul_penc_inversion
    obtain ⟨ka,na,pa,hsa⟩ := ha ⟨key,ra,ma,hea⟩
    obtain ⟨kb,nb,pb,hsb⟩ := hb ⟨key,rb,mb,heb⟩
    have hsyntaxA := expanded_minimum_ciphertext_syntax ns swap left right rs hn ns.restricted a
      (hm.subterm (.binaryLeft .mul .hole b)) hsa
    have hsyntaxB := expanded_minimum_ciphertext_syntax ns swap left right rs hn ns.restricted b
      (hm.subterm (.binaryRight .mul a .hole)) hsb
    obtain ⟨ar,hapub,hasize,hak,an,ap,hav⟩ := expanded_ciphertext_syntax_key_transfer ns swap' swap left right rs hn' a
      hsyntaxA hm.isPublic.1 (hobs.symm.mono (by simp only [Term.nodeCount]; omega)) hea
    obtain ⟨br,hbpub,hbsize,hbk,bn,bp,hbv⟩ := expanded_ciphertext_syntax_key_transfer ns swap' swap left right rs hn' b
      hsyntaxB hm.isPublic.2 (hobs.symm.mono (by simp only [Term.nodeCount]; omega)) heb
    have hkey := (hobs ar br hapub hbpub (by simp only [Term.nodeCount]; omega)).mpr (hak.trans hbk.symm)
    exact ⟨_,_,_,(EqE.binary .mul hav (hbv.trans (.ternary .penc hkey.symm (.refl _) (.refl _)))).trans
      (RootStep.homomorphic _ _ _ _ _).sound⟩
  · intro a b hm ha hb hobs out hmatch
    obtain ⟨j,_,hout⟩ := expanded_minimum_decryption_match_result_of_reflection ns swap swap' left right rs hn
      a b hm ha hb hobs hmatch
    obtain ⟨number,hnum⟩ := hn' j
    have he := hout.trans hnum
    have hx := numeric_not_data_shapes number
    exact ⟨fun ⟨x,y,h⟩ => hx.1 ⟨x,y,he.symm.trans h⟩,
      fun ⟨k,s,m,h⟩ => hx.2.1 ⟨k,s,m,he.symm.trans h⟩,
      fun ⟨k,c,h⟩ => hx.2.2 ⟨k,c,he.symm.trans h⟩⟩

/-- Both directions of all three value classes for source-minimum recipes. -/
theorem expanded_minimum_value_shapes_swap (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (hn' : ExpandedResultsNumeric ns swap' left right rs) (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount) :
    (((expandedFrame ns swap left right rs).eval r).PairValue ↔ ((expandedFrame ns swap' left right rs).eval r).PairValue) ∧
    (((expandedFrame ns swap left right rs).eval r).CiphertextValue ↔ ((expandedFrame ns swap' left right rs).eval r).CiphertextValue) ∧
    (((expandedFrame ns swap left right rs).eval r).PartialValue ↔ ((expandedFrame ns swap' left right rs).eval r).PartialValue) := by
  have href := expanded_minimum_value_shape_reflection ns swap swap' left right rs hn hn' r hm hobs
  have hf := expanded_minimum_passive_values_forward ns swap swap' left right rs hn r hm
  refine ⟨⟨hf.1,href.1⟩,⟨?_,href.2.1⟩,⟨hf.2,href.2.2⟩⟩
  rintro ⟨key,nonce,message,he⟩
  obtain ⟨_,_,_,_,s,p,hv⟩ := expanded_minimum_ciphertext_key_transfer ns swap swap' left right rs hn r hm hobs he
  exact ⟨_,s,p,hv⟩

/-- Accepted public submissions discharge both numeric-result hypotheses. -/
theorem accepted_expanded_minimum_value_shapes_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount) :
    (((expandedFrame ns swap left right rs).eval r).PairValue ↔ ((expandedFrame ns swap' left right rs).eval r).PairValue) ∧
    (((expandedFrame ns swap left right rs).eval r).CiphertextValue ↔ ((expandedFrame ns swap' left right rs).eval r).CiphertextValue) ∧
    (((expandedFrame ns swap left right rs).eval r).PartialValue ↔ ((expandedFrame ns swap' left right rs).eval r).PartialValue) :=
  expanded_minimum_value_shapes_swap ns swap swap' left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap)
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap') r hm hobs

/-- After simultaneous reflection, the remaining destination decryption case
is an actual borrowed E6 slot with its numeric result. It is not a failure theorem. -/
theorem accepted_expanded_minimum_decryption_match_numeric (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (Term.binary .dec a b).nodeCount) {message : Ground}
    (hmatch : DecryptionMatch ((expandedFrame ns swap' left right rs).eval a)
      ((expandedFrame ns swap' left right rs).eval b) message) :
    ∃ j : Fin (n+1), a = .var (expandedPartial j) ∧ EqE message (tallyResult ns swap' left right rs j) ∧
      ∃ number, EqE message (addNumeral number) := by
  have hsa := accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha a
    (hm.subterm (.binaryLeft .dec .hole b)) (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hsb := accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha b
    (hm.subterm (.binaryRight .dec a .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega))
  obtain ⟨j,hj,hout⟩ := expanded_minimum_decryption_match_result_of_reflection ns swap swap' left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) a b hm hsa.2.2.mpr hsb.2.1.mpr hobs hmatch
  obtain ⟨number,hnum⟩ := accepted_expanded_results_numeric ns hf left right rs hp ha swap' j
  exact ⟨j,hj,hout,number,hout.trans hnum⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
