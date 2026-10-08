import ExplainableCrypto.Helios.Symbolic.ExpandedAtomicOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Atomic minima preserve their full-E value when the actual result slots
agree. The conclusion is equational, not raw syntactic evaluation equality. -/
theorem expanded_minimum_atomic_value_transfer (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (hresults : ∀ j, EqE (tallyResult ns swap left right rs j) (tallyResult ns swap' left right rs j))
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (t : Ground) (ht : t.nodeCount = 1) (he : EqE ((expandedFrame ns swap left right rs).eval r) t) :
    EqE ((expandedFrame ns swap' left right rs).eval r) t := by
  rcases ground_atom_cases ht with ⟨name,rfl⟩ | ⟨c,rfl⟩
  · rw [expanded_minimum_name_form ns swap left right rs hp hn r hm name he]
    exact .refl _
  · rcases expanded_minimum_constant_form ns swap left right rs ns.restricted r hm c he with rfl | ⟨j,rfl,hc⟩
    · exact .refl _
    · simpa only [Frame.eval,Term.subst,expanded_frame_result] using (hresults j).symm.trans hc

/-- Accepted elections supply both numeric results and their cross-world
equality. Atomic values require no smaller-observation induction premise. -/
theorem accepted_expanded_minimum_atomic_value_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (t : Ground) (ht : t.nodeCount = 1) (he : EqE ((expandedFrame ns swap left right rs).eval r) t) :
    EqE ((expandedFrame ns swap' left right rs).eval r) t := by
  apply expanded_minimum_atomic_value_transfer ns swap swap' left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ?_ r hm t ht he
  intro j
  obtain ⟨number,_,hv⟩ := accepted_sequence_tally_numeric ns hf left right rs hp ha j
  exact (hv swap).trans (hv swap').symm

/-- The destination observes exact equality of the supplied ground atoms,
including literal/result-handle aliases and different constant symbols. -/
theorem accepted_expanded_minimum_atomic_equality_iff (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    (a b : Ground) (hatom : a.nodeCount = 1) (hbatom : b.nodeCount = 1)
    (her : EqE ((expandedFrame ns swap left right rs).eval r) a)
    (hes : EqE ((expandedFrame ns swap left right rs).eval s) b) :
    EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) ↔ a = b := by
  have hv := accepted_expanded_minimum_atomic_value_transfer ns hf swap swap' left right rs hp ha r hr a hatom her
  have hw := accepted_expanded_minimum_atomic_value_transfer ns hf swap swap' left right rs hp ha s hs b hbatom hes
  have htest : EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) ↔ EqE a b :=
    ⟨fun h => hv.symm.trans (h.trans hw),fun h => hv.trans (h.trans hw.symm)⟩
  exact htest.trans (EqE.ground_atoms_iff a b hatom hbatom)

/-- Complete minimum atomic observation branch, with all publication premises
discharged by acceptance and no residual smaller-test hypothesis. -/
theorem accepted_expanded_minimum_atomic_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s)
    (a b : Ground) (hatom : a.nodeCount = 1) (hbatom : b.nodeCount = 1)
    (her : EqE ((expandedFrame ns false left right rs).eval r) a)
    (hes : EqE ((expandedFrame ns false left right rs).eval s) b) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
      EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  (accepted_expanded_minimum_atomic_equality_iff ns hf false false left right rs hp ha r s hr hs a b hatom hbatom her hes).trans
    (accepted_expanded_minimum_atomic_equality_iff ns hf false true left right rs hp ha r s hr hs a b hatom hbatom her hes).symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
