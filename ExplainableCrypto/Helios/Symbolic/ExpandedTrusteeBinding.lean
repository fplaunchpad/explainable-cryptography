import ExplainableCrypto.Helios.Symbolic.ExpandedPublicDecryption
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulDecryptionTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The remaining borrowed-E6 obligation: transfer a minimum ciphertext's
complete match to a published tally binding, within the original induction bound. -/
def ExpandedTrusteeBindingTransport (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) : Prop :=
  ∀ (j : Fin (n+1)) (b : Recipe (ExpandedHandles n)),
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b →
    EqE ((expandedFrame ns swap left right rs).eval b) (tallyCiphertext ns swap left right rs j) →
    Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (Term.binary .dec (.var (expandedPartial j)) b).nodeCount →
    Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs)
      (Term.binary .dec (.var (expandedPartial j)) b).nodeCount →
    EqE ((expandedFrame ns swap' left right rs).eval b) (tallyCiphertext ns swap' left right rs j)

/-- For every retained old public recipe, complete tally binding already
transfers by B7, without minimum size, acceptance or smaller-test premises. -/
theorem expanded_old_tally_binding_swap (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (r : Recipe 3) (hr : r.Public ns.restricted) (j : Fin (n+1)) :
    EqE ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (expandedOld i))))
      (tallyCiphertext ns swap left right rs j) ↔
    EqE ((expandedFrame ns swap' left right rs).eval (r.subst (fun i => .var (expandedOld i))))
      (tallyCiphertext ns swap' left right rs j) := by
  simpa only [expanded_old_recipe_value,tallyCiphertext] using
    expanded_old_equality_swap ns hf swap swap' left right rs r (tallyRecipe rs j) hr (tallyRecipe_public rs j ns.restricted hp)

/-- Full binding in both assignments shares the actual one-node result slot.
This statement isolates E6 without suppressing separate structured-key E5 uses. -/
theorem expanded_bound_tally_shared (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1))
    (b : Recipe (ExpandedHandles n))
    (hb : EqE ((expandedFrame ns swap left right rs).eval b) (tallyCiphertext ns swap left right rs j))
    (hb' : EqE ((expandedFrame ns swap' left right rs).eval b) (tallyCiphertext ns swap' left right rs j)) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (.binary .dec (.var (expandedPartial j)) b) := by
  refine ⟨.var (expandedResult j),.of_nodeCount_one trivial rfl,?_,?_⟩
  · simpa only [Frame.eval,Term.subst,expanded_frame_partial,expanded_frame_result,tallyResult] using
      EqE.binary .dec (.refl (tallyPartial ns swap left right rs j)) hb
  · simpa only [Frame.eval,Term.subst,expanded_frame_partial,expanded_frame_result,tallyResult] using
      EqE.binary .dec (.refl (tallyPartial ns swap' left right rs j)) hb'

/-- Ordinary E5 and public-constructor E6 are discharged. Only a borrowed
partial slot invokes the remaining complete-tally-binding transport. -/
theorem accepted_expanded_minimum_children_decryption_shared_of_trustee_binding (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hbinding : ExpandedTrusteeBindingTransport ns swap swap' left right rs)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hforward : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (Term.binary .dec a b).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs)
      (Term.binary .dec a b).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.binary .dec a b) := by
  classical
  have hn := accepted_expanded_results_numeric ns hf left right rs hp haccept swap
  have hobs := accepted_expanded_observationsBelow_of_two_way_minima ns hf swap swap' left right rs hp haccept _ hforward hreverse
  by_cases hs : ∃ out, DecryptionMatch ((expandedFrame ns swap left right rs).eval a) ((expandedFrame ns swap left right rs).eval b) out
  · obtain ⟨k,nonce,message,hcipher,hkey⟩ := (DecryptionMatch.exists_iff_values _ _).mp hs
    rcases hkey with hd | hpartial
    · have hc := hcipher.trans (.ternary .penc (.unary .pk hd.symm) (.refl _) (.refl _))
      obtain ⟨key,r,p,rfl⟩ := expanded_minimum_ciphertext_public_secret_form ns swap left right rs hp hn b a hb ha.isPublic hc
      obtain ⟨out,hout⟩ := hs
      exact ⟨p,hb.subterm (.ternaryThird .penc key r .hole),hout.reduces.sound.trans hout.explicit_plaintext.symm,
        public_key_constructed_decryption_transfer _ _ a key r p ha.isPublic hb.isPublic hobs
          ((EqE.penc_iff _ _ _ _ _ _).mp hc).1⟩
    · rcases expanded_minimum_partial_decryption_form ns swap left right rs hn ns.restricted a ha hpartial with
        ⟨u,v,rfl⟩ | ⟨j,rfl⟩
      · have hk := ((EqE.partialDecrypt_iff _ _ _ _).mp hpartial).1
        have hc := hcipher.trans (.ternary .penc (.unary .pk hk.symm) (.refl _) (.refl _))
        obtain ⟨key,r,p,rfl⟩ := expanded_minimum_ciphertext_public_secret_form ns swap left right rs hp hn b u hb ha.isPublic.1 hc
        obtain ⟨out,hout⟩ := hs
        exact ⟨p,hb.subterm (.ternaryThird .penc key r .hole),hout.reduces.sound.trans hout.explicit_plaintext.symm,
          public_partial_constructed_decryption_transfer _ _ u v key r p ha.isPublic hb.isPublic hobs ⟨out,hout⟩⟩
      · have hbind : EqE ((expandedFrame ns swap left right rs).eval b) (tallyCiphertext ns swap left right rs j) := by
          simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial] at hpartial
          exact ((EqE.partialDecrypt_iff _ _ _ _).mp hpartial).2.symm
        exact expanded_bound_tally_shared ns swap swap' left right rs j b hbind (hbinding j b hb hbind hforward hreverse)
  · exact .of_minimal (expanded_minimum_stuck_decryption_of_children ns swap left right rs hn ns.restricted a b ha hb
      (fun out he => hs ⟨out,he⟩))

/-- The last local operator now requires only complete borrowed tally binding. -/
theorem accepted_expanded_successful_decryption_of_trustee_binding (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hbinding : ExpandedTrusteeBindingTransport ns swap swap' left right rs) :
    Frame.SuccessfulDecryptionTransport (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) := by
  intro r _ hc _ hv hforward hreverse
  cases r with
  | name _ | var _ | const _ | unary _ _ | ternary _ _ _ _ | spk _ _ _ _ => cases hv
  | binary f a b =>
    cases f with
    | pair | mul | add | compose | partialDecrypt => cases hv
    | dec =>
      exact accepted_expanded_minimum_children_decryption_shared_of_trustee_binding ns hf swap swap' left right rs hp haccept
        hbinding a b hc.1 hc.2 hforward hreverse

/-- Complete borrowed-binding transfer in both directions suffices for the
expanded static-equivalence target; all other local cases are discharged. -/
theorem accepted_expanded_staticEq_of_trustee_binding (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : ExpandedTrusteeBindingTransport ns false true left right rs)
    (hreverse : ExpandedTrusteeBindingTransport ns true false left right rs) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) :=
  accepted_expanded_staticEq_of_successful_decryption_transport ns hf left right rs hp haccept
    (accepted_expanded_successful_decryption_of_trustee_binding ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_successful_decryption_of_trustee_binding ns hf true false left right rs hp haccept hreverse)

/-- Complete borrowed-binding transfer in both directions suffices for the
partial static-equivalence target; all other local cases are discharged. -/
theorem accepted_partial_staticEq_of_trustee_binding (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : ExpandedTrusteeBindingTransport ns false true left right rs)
    (hreverse : ExpandedTrusteeBindingTransport ns true false left right rs) :
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) :=
  accepted_partial_staticEq_of_successful_decryption_transport ns hf left right rs hp haccept
    (accepted_expanded_successful_decryption_of_trustee_binding ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_successful_decryption_of_trustee_binding ns hf true false left right rs hp haccept hreverse)

/-- Complete borrowed-binding transfer in both directions suffices for the
final static-equivalence target; all other local cases are discharged. -/
theorem accepted_final_staticEq_of_trustee_binding (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : ExpandedTrusteeBindingTransport ns false true left right rs)
    (hreverse : ExpandedTrusteeBindingTransport ns true false left right rs) :
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) :=
  accepted_final_staticEq_of_successful_decryption_transport ns hf left right rs hp haccept
    (accepted_expanded_successful_decryption_of_trustee_binding ns hf false true left right rs hp haccept hforward)
    (accepted_expanded_successful_decryption_of_trustee_binding ns hf true false left right rs hp haccept hreverse)

end ExplainableCrypto.Helios.Symbolic.Historical.General
