import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionSummary

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Complete addition-valued equality branch for source-minimum recipes in
actual accepted expanded frames. Shared tally numbers are derived from accepted
submissions, and all residual atom comparisons are strictly smaller than the
original pair. This includes published numeric handles and numeric collapses. -/
theorem accepted_expanded_minimum_addition_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    {x y u v : Ground}
    (her : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .add x y))
    (hes : EqE ((expandedFrame ns swap left right rs).eval s) (.binary .add u v))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s) ↔
      EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) := by
  choose numbers _ hnum using fun j => accepted_sequence_tally_numeric ns hf left right rs hp ha j
  let ν := expandedNumericHandles numbers
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  have hrform := expanded_minimum_add_form ns swap left right rs hn ns.restricted r hr her
  have hsform := expanded_minimum_add_form ns swap left right rs hn ns.restricted s hs hes
  have har := accepted_expanded_minimum_add_numeric_leaf_values ns hf swap swap' left right rs hp ha numbers r s hr hrform hobs
  have has := accepted_expanded_minimum_add_numeric_leaf_values ns hf swap swap' left right rs hp ha numbers s r hs hsform
    (by simpa only [Nat.add_comm] using hobs)
  have hrf := Term.addNumericValue_summary (expandedFrame ns swap left right rs).value ν r har.1
  have hsf := Term.addNumericValue_summary (expandedFrame ns swap left right rs).value ν s has.1
  have hrt := Term.addNumericValue_summary (expandedFrame ns swap' left right rs).value ν r har.2
  have hst := Term.addNumericValue_summary (expandedFrame ns swap' left right rs).value ν s has.2
  have hsource := eqE_iff_add_value_summary _ _ hrf.2 hsf.2
  have htarget := eqE_iff_add_value_summary _ _ hrt.2 hst.2
  rw [hrf.1,hsf.1] at hsource
  rw [hrt.1,hst.1] at htarget
  have hsummary := expanded_add_numeric_summary_transfer numbers _ _ r s hr.isPublic hs.isPublic hrform hsform hobs
  have heq (world : Bool) (a : Recipe (ExpandedHandles n)) :
      EqE ((expandedFrame ns world left right rs).eval a)
        (a.addNumericValue (expandedFrame ns world left right rs).value ν) :=
    Term.addNumericValue_eq _ ν (expanded_numeric_handle_value ns world left right rs numbers (fun j => hnum j world)) a
  have bridge (world : Bool) :
      EqE ((expandedFrame ns world left right rs).eval r) ((expandedFrame ns world left right rs).eval s) ↔
        EqE (r.addNumericValue (expandedFrame ns world left right rs).value ν)
          (s.addNumericValue (expandedFrame ns world left right rs).value ν) :=
    ⟨fun he => (heq world r).symm.trans (he.trans (heq world s)),
      fun he => (heq world r).trans (he.trans (heq world s).symm)⟩
  exact (bridge swap).trans (hsource.trans (hsummary.trans (htarget.symm.trans (bridge swap').symm)))

end ExplainableCrypto.Helios.Symbolic.Historical.General
