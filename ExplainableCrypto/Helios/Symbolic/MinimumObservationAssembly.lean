import ExplainableCrypto.Helios.Symbolic.NormalDestructorExclusions
import ExplainableCrypto.Helios.Symbolic.LocalMinimumTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- All common normal-value branches assemble into forward equality preservation.
Both recipes are source-minimum. The smaller-observation premise remains explicit;
no destination minimum, chosen head, or normal representative is supplied. -/
theorem minimum_equality_forward (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount))
    (he : EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s)) :
    EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨t, hp, ht⟩ := exists_normal_form ((frame ns false left right).eval r)
  have her := hp.sound
  have hes := he.symm.trans her
  have transfer (h : EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s)) := h.mp he
  cases t with
  | name a =>
    exact transfer (minimum_atomic_equality_swap ns left right r s hr hs
      (.name a) (.name a) rfl rfl her hes)
  | const c =>
    exact transfer (minimum_atomic_equality_swap ns left right r s hr hs
      (.const c) (.const c) rfl rfl her hes)
  | var v => exact nomatch v
  | unary f a =>
    cases f with
    | pk => exact transfer (minimum_public_key_equality_swap ns left right r s hr hs her hes hobs)
    | fst =>
      have hn := ht.projection_no_pair (Or.inl rfl)
      exact transfer (minimum_stuck_projection_equality_swap ns left right r s hr hs
        .fst .fst (Or.inl rfl) (Or.inl rfl) hn hn her hes hobs)
    | snd =>
      have hn := ht.projection_no_pair (Or.inr rfl)
      exact transfer (minimum_stuck_projection_equality_swap ns left right r s hr hs
        .snd .snd (Or.inr rfl) (Or.inr rfl) hn hn her hes hobs)
  | binary f a b =>
    cases f with
    | pair => exact transfer (minimum_pair_equality_swap ns hf left right r s hr hs her hes hobs)
    | partialDecrypt =>
      exact transfer (minimum_partial_decryption_equality_swap ns left right r s hr hs her hes hobs)
    | dec =>
      exact transfer (minimum_stuck_decryption_equality_swap ns left right r s hr hs
        ht.decryption_no_match ht.decryption_no_match her hes hobs)
    | compose => exact transfer (minimum_composition_equality_swap ns left right r s hr hs her hes hobs)
    | add => exact transfer (minimum_addition_equality_swap ns left right r s hr hs her hes hobs)
    | mul =>
      have hnr : ¬ ((frame ns false left right).eval r).CiphertextValue := by
        rintro ⟨k, nonce, p, hv⟩
        exact ht.mul_not_ciphertext ⟨k, nonce, p, her.symm.trans hv⟩
      have hns : ¬ ((frame ns false left right).eval s).CiphertextValue := by
        rintro ⟨k, nonce, p, hv⟩
        exact ht.mul_not_ciphertext ⟨k, nonce, p, hes.symm.trans hv⟩
      exact transfer (minimum_non_ciphertext_multiplication_equality_swap ns left right r s hr hs
        her hes hnr hns hobs)
  | ternary f a b c =>
    cases f with
    | penc => exact transfer (minimum_ciphertext_equality_swap ns hf left right r s hr hs her hes hobs)
    | checkspk =>
      exact transfer (minimum_stuck_check_equality_swap ns left right r s hr hs
        ht.proof_check_no_match ht.proof_check_no_match her hes hobs)
  | spk a b c d => exact transfer (minimum_proof_equality_swap ns hf left right r s hr hs her hes hobs)

/-- With minimum size in both worlds, the forward assembly also handles reverse
observations by exchanging the candidate assignments. This does not infer
that a source minimum remains minimum after the swap. -/
theorem minimum_equality_swap_of_both_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    (hr' : MinimalRecipe ns.restricted (frame ns true left right).value r)
    (hs' : MinimalRecipe ns.restricted (frame ns true left right).value s)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) :=
  ⟨minimum_equality_forward ns hf left right r s hr hs hobs,
    minimum_equality_forward ns hf right left r s hr' hs' hobs.symm⟩

/-- Reverse shared minimization supplies the destination minima required by the
assembled step. It is a logical premise about every public recipe. -/
theorem minimum_observation_step_of_reverse_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hreverse : Frame.CommonMinima (frame ns true left right) (frame ns false left right)) :
    Frame.MinimumObservationStep (frame ns false left right) (frame ns true left right) := by
  intro r s hr hs hobs
  exact minimum_equality_swap_of_both_minima ns hf left right r s hr hs
    (hreverse.minimum_destination hr) (hreverse.minimum_destination hs) hobs

/-- For the fresh initial historical frames, shared minimization in both
orientations is exactly the remaining static-equivalence obligation. -/
theorem staticEq_iff_common_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) ↔
      Frame.CommonMinima (frame ns false left right) (frame ns true left right) ∧
      Frame.CommonMinima (frame ns true left right) (frame ns false left right) := by
  constructor
  · intro h
    exact ⟨h.common_minima, h.symm.common_minima⟩
  · rintro ⟨hforward, hreverse⟩
    exact Frame.staticEq_of_common_minima hforward
      (minimum_observation_step_of_reverse_minima ns hf left right hreverse)

/-- Local root minimization with minimum children, in both orientations, now
suffices for initial-frame static equivalence. No observation premise remains
in this interface; the two local transport premises remain to be proved. -/
theorem staticEq_of_local_transport_both (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty)
    (hforward : Frame.LocalMinimumTransport (frame ns false left right) (frame ns true left right))
    (hreverse : Frame.LocalMinimumTransport (frame ns true left right) (frame ns false left right)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) :=
  (staticEq_iff_common_minima ns hf left right).mpr
    ⟨Frame.common_minima_of_local hforward, Frame.common_minima_of_local hreverse⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
