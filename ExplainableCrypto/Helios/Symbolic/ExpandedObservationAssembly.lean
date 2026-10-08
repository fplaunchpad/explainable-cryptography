import ExplainableCrypto.Helios.Symbolic.ExpandedCiphertextTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedMulTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedCompositionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedStuckTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedAtomicTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedPairTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedProofTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedPartialTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedCheckOrigins
import ExplainableCrypto.Helios.Symbolic.NormalDestructorExclusions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- All expanded normal-value branches assemble into forward equality. Source
minimum size and strictly smaller public observations remain explicit; no
normal form, value class or destination minimum is supplied by the caller. -/
theorem accepted_expanded_minimum_equality_forward (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s)
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow
      (expandedFrame ns true left right rs) (r.nodeCount+s.nodeCount))
    (he : EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s)) :
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) := by
  obtain ⟨t,htpath,ht⟩ := exists_normal_form ((expandedFrame ns false left right rs).eval r)
  have her := htpath.sound
  have hes := he.symm.trans her
  have transfer (h : EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
      EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s)) := h.mp he
  cases t with
  | name a => exact transfer (accepted_expanded_minimum_atomic_equality_swap ns hf left right rs hp ha
      r s hr hs (.name a) (.name a) rfl rfl her hes)
  | const c => exact transfer (accepted_expanded_minimum_atomic_equality_swap ns hf left right rs hp ha
      r s hr hs (.const c) (.const c) rfl rfl her hes)
  | var v => exact nomatch v
  | unary f a =>
    cases f with
    | pk => exact transfer (accepted_expanded_minimum_public_key_equality_swap ns hf left right rs hp ha r s hr hs her hes hobs)
    | fst =>
      have hn := ht.projection_no_pair (Or.inl rfl)
      exact transfer (accepted_expanded_minimum_stuck_projection_equality_swap ns hf false true left right rs hp ha
        r s hr hs .fst .fst (Or.inl rfl) (Or.inl rfl) hn hn her hes hobs)
    | snd =>
      have hn := ht.projection_no_pair (Or.inr rfl)
      exact transfer (accepted_expanded_minimum_stuck_projection_equality_swap ns hf false true left right rs hp ha
        r s hr hs .snd .snd (Or.inr rfl) (Or.inr rfl) hn hn her hes hobs)
  | binary f a b =>
    cases f with
    | pair => exact transfer (accepted_expanded_minimum_pair_equality_swap ns hf left right rs hp ha r s hr hs her hes hobs)
    | partialDecrypt => exact transfer (expanded_minimum_partial_equality_swap ns hf left right rs hp ha r s hr hs her hes hobs)
    | dec => exact transfer (accepted_expanded_minimum_stuck_decryption_equality_swap ns hf false true left right rs hp ha
        r s hr hs ht.decryption_no_match ht.decryption_no_match her hes hobs)
    | compose => exact transfer (accepted_expanded_minimum_composition_equality_swap ns hf false true left right rs hp ha
        r s hr hs her hes hobs)
    | add => exact transfer (accepted_expanded_minimum_addition_equality_swap ns hf false true left right rs hp ha
        r s hr hs her hes hobs)
    | mul =>
      have hnr : ¬ ((expandedFrame ns false left right rs).eval r).CiphertextValue := by
        rintro ⟨k,nonce,p,hv⟩
        exact ht.mul_not_ciphertext ⟨k,nonce,p,her.symm.trans hv⟩
      have hns : ¬ ((expandedFrame ns false left right rs).eval s).CiphertextValue := by
        rintro ⟨k,nonce,p,hv⟩
        exact ht.mul_not_ciphertext ⟨k,nonce,p,hes.symm.trans hv⟩
      exact transfer (accepted_expanded_minimum_non_ciphertext_multiplication_equality_swap ns hf false true left right rs hp ha
        r s hr hs her hes hnr hns hobs)
  | ternary f a b c =>
    cases f with
    | penc => exact transfer (accepted_expanded_minimum_ciphertext_equality_swap ns hf false true left right rs hp ha
        r s hr hs ⟨a,b,c,her⟩ ⟨a,b,c,hes⟩ hobs)
    | checkspk => exact transfer (accepted_expanded_minimum_stuck_check_equality_swap ns hf left right rs hp ha
        r s hr hs ht.proof_check_no_match ht.proof_check_no_match her hes hobs)
  | spk a b c d => exact transfer (accepted_expanded_minimum_proof_equality_swap ns hf left right rs hp ha r s hr hs her hes hobs)

/-- Initial-frame static equivalence transfers actual sequential acceptance
before reversing candidate assignments in the expanded proof. -/
theorem accepted_sequence_reversed_candidates (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    (frame ns false right left).AcceptsSequence n (.var 0) honestBoardRecipes rs :=
  (initial_acceptsSequence_iff ns hf left right honestBoardRecipes rs
    (by intro r hr; simp [honestBoardRecipes] at hr; rcases hr with rfl | rfl <;> trivial) hp).mp ha

/-- Both source and destination minima give the full comparison iff. The
reverse proof derives its acceptance premise; it never assumes minimum size
persists across the vote swap. -/
theorem accepted_expanded_minimum_equality_swap_of_both_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s)
    (hr' : MinimalRecipe ns.restricted (expandedFrame ns true left right rs).value r)
    (hs' : MinimalRecipe ns.restricted (expandedFrame ns true left right rs).value s)
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow
      (expandedFrame ns true left right rs) (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
      EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  ⟨accepted_expanded_minimum_equality_forward ns hf left right rs hp ha r s hr hs hobs,
    accepted_expanded_minimum_equality_forward ns hf right left rs hp
      (accepted_sequence_reversed_candidates ns hf left right rs hp ha) r s hr' hs' hobs.symm⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
