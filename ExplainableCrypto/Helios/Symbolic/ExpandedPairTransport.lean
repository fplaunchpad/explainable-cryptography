import ExplainableCrypto.Helios.Symbolic.ExpandedPairOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Exact nonempty-tail identity is inherited from the original ballot values.
The bound excludes the coincident empty tails. No new publication assumption is needed. -/
theorem expanded_ballot_tail_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i j : Fin 2) (k l : Nat)
    (hk : k < fieldCount n) (hl : l < fieldCount n) :
    EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).drop k))
      ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld j.succ)).drop l)) ↔ i = j ∧ k = l := by
  simpa only [Frame.eval,Term.subst_drop,Term.subst,expanded_frame_old] using
    ballot_tail_equality_iff ns hf swap left right i j k l hk hl

/-- All pair-form comparisons preserve both ordered projections. Both borrowed
sides reuse old tail identity; either constructed side uses strictly smaller tests. -/
theorem expanded_pair_form_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r s : Recipe (ExpandedHandles n))
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted)
    (hfr : ExpandedPairObservationForm r) (hfs : ExpandedPairObservationForm s)
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) := by
  rcases hfr with ⟨a,b,rfl⟩ | ⟨i,k,hk,rfl⟩
  · exact constructed_pair_equality_transfer _ _ a b s hr hs
      (hfs.pair_value ns false left right rs) (hfs.pair_value ns true left right rs) hobs
  · rcases hfs with ⟨a,b,rfl⟩ | ⟨j,l,hl,rfl⟩
    · have h := constructed_pair_equality_transfer (expandedFrame ns false left right rs) (expandedFrame ns true left right rs)
        a b ((Term.var (expandedOld i.succ)).drop k) hs hr
        (expanded_ballot_tail_pair_value ns false left right rs i k hk)
        (expanded_ballot_tail_pair_value ns true left right rs i k hk)
        (by simpa only [Nat.add_comm] using hobs)
      exact ⟨fun he => (h.mp he.symm).symm,fun he => (h.mpr he.symm).symm⟩
    · exact (expanded_ballot_tail_equality_iff ns hf false left right rs i j k l hk hl).trans
        (expanded_ballot_tail_equality_iff ns hf true left right rs i j k l hk hl).symm

/-- Source minima derive both exact forms and destination pair-valuedness.
The intended smaller-observation premise is the only observation hypothesis. -/
theorem expanded_minimum_pair_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns false left right rs) (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s) {a b c d : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.binary .pair a b))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.binary .pair c d))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_pair_form_equality_swap ns hf left right rs r s hr.isPublic hs.isPublic
    (expanded_minimum_pair_observation_form ns false left right rs hn ns.restricted r hr her)
    (expanded_minimum_pair_observation_form ns false left right rs hn ns.restricted s hs hes) hobs

theorem accepted_expanded_minimum_pair_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s) {a b c d : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.binary .pair a b))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.binary .pair c d))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_minimum_pair_equality_swap ns hf left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha false) r s hr hs her hes hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
