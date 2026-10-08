import ExplainableCrypto.Helios.Symbolic.ExpandedValueShapes

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A result-handle observation excludes the remaining borrowed E6 success.
The strict budget is the whole decryption size plus two: the public test itself
has size plus one. This allowance is explicit, not part of shape reflection. -/
theorem accepted_expanded_minimum_decryption_failure_with_result_probe (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      ((Term.binary .dec a b).nodeCount + 2)) :
    ∀ out, ¬ DecryptionMatch ((expandedFrame ns swap' left right rs).eval a)
      ((expandedFrame ns swap' left right rs).eval b) out := by
  intro out hmatch
  obtain ⟨j,_,hout,_⟩ := accepted_expanded_minimum_decryption_match_numeric ns hf swap swap' left right rs hp ha
    a b hm (hobs.mono (by omega)) hmatch
  have hprobe' : EqE ((expandedFrame ns swap' left right rs).eval (.binary .dec a b))
      ((expandedFrame ns swap' left right rs).eval (.var (expandedResult j))) := by
    simp only [Frame.eval,Term.subst,expanded_frame_result]
    exact hmatch.reduces.sound.trans hout
  have hprobe := (hobs (.binary .dec a b) (.var (expandedResult j)) hm.isPublic trivial
    (by simp only [Term.nodeCount]; omega)).mpr hprobe'
  have hsize := hm.least (.var (expandedResult j)) trivial hprobe
  have := a.nodeCount_pos
  have := b.nodeCount_pos
  simp only [Term.nodeCount] at hsize
  omega

/-- The complete syntactic minimum-decryption equality branch. The ordinary
sum-of-recipe-sizes observation budget pays for both result-handle probes,
because every decryption has at least three nodes. -/
theorem accepted_expanded_minimum_decryption_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b c d : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec c d))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      ((Term.binary .dec a b).nodeCount + (Term.binary .dec c d).nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval (.binary .dec a b))
      ((expandedFrame ns swap left right rs).eval (.binary .dec c d)) ↔
    EqE ((expandedFrame ns swap' left right rs).eval (.binary .dec a b))
      ((expandedFrame ns swap' left right rs).eval (.binary .dec c d)) := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  have hnr := expanded_minimum_decryption_no_match ns swap left right rs hn ns.restricted a b hr
  have hns := expanded_minimum_decryption_no_match ns swap left right rs hn ns.restricted c d hs
  have hnr' := accepted_expanded_minimum_decryption_failure_with_result_probe ns hf swap swap' left right rs hp ha a b hr
    (hobs.mono (by have := c.nodeCount_pos; have := d.nodeCount_pos; simp only [Term.nodeCount]; omega))
  have hns' := accepted_expanded_minimum_decryption_failure_with_result_probe ns hf swap swap' left right rs hp ha c d hs
    (hobs.mono (by have := a.nodeCount_pos; have := b.nodeCount_pos; simp only [Term.nodeCount]; omega))
  have hac := hobs a c hr.isPublic.1 hs.isPublic.1 (by simp only [Term.nodeCount]; omega)
  have hbd := hobs b d hr.isPublic.2 hs.isPublic.2 (by simp only [Term.nodeCount]; omega)
  exact (EqE.decryption_iff_of_no_match _ _ _ _ hnr hns).trans
    ((and_congr hac hbd).trans (EqE.decryption_iff_of_no_match _ _ _ _ hnr' hns').symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
