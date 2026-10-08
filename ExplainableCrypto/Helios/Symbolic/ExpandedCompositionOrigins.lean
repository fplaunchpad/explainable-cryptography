import ExplainableCrypto.Helios.Symbolic.CompositionOriginTools
import ExplainableCrypto.Helios.Symbolic.ExpandedValueShapes
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulProjections

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- No numeral has a composition E-value, including sums above one. -/
theorem numeric_not_composition (number : Nat) (x y : Ground) :
    ¬ EqE (addNumeral number) (.binary .compose x y) := by
  intro he
  obtain ⟨_,_,hh⟩ := he.symm.compose_irreducible_shape (addNumeral_irreducible number)
  cases number <;> cases hh

/-- Actual partial and numeric result handles cannot hide a composition. -/
theorem expanded_handle_not_composition (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n)) (x y : Ground) :
    ¬ EqE ((expandedFrame ns swap left right rs).value v) (.binary .compose x y) := by
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro he
    have hv : EqE ((frame ns swap left right).value old) (.binary .compose x y) := by
      simpa only [expandedFrame,Fin.addCases_left] using he
    fin_cases old
    · exact arithmetic_not_eqE_pk .compose (Or.inr rfl) _ _ _ hv.symm
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
      exact arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp)
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
      exact arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro he
      have hv : EqE (tallyPartial ns swap left right rs j) (.binary .compose x y) := by
        simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using he
      exact arithmetic_not_eqE_passive_binary .compose .partialDecrypt (Or.inr rfl) (Or.inr rfl) _ _ _ _ hv.symm
    · intro he
      obtain ⟨number,hnum⟩ := hn j
      exact numeric_not_composition number x y (hnum.symm.trans
        (by simpa only [expandedFrame,Fin.addCases_right] using he))

/-- A source-minimum composition value has exact compose syntax. The caller's
public-name policy is preserved independently of the frame policy. -/
theorem expanded_minimum_compose_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {x y : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .compose x y)) :
    ∃ a b, r = .binary .compose a b := by
  apply (expandedFrame ns swap left right rs).compose_form_of_paths r
    (expanded_handle_not_composition ns swap left right rs hn) ?_ ?_ he
  · intro a b hr out hmatch
    subst r
    exact False.elim (expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out hmatch)
  · intro f a hr hf hv
    obtain ⟨x,y,hpair⟩ := hv
    subst r
    exact (expanded_minimum_successful_projection_form ns swap left right rs hn restricted f hf a hm hpair).data_value ns swap left right rs

/-- After-swap origins use the recipe-only observation budget. Borrowed E6
success is allowed and excluded by its numeric output, not by a larger probe. -/
theorem accepted_expanded_minimum_compose_form_after_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount)
    {x y : Ground} (he : EqE ((expandedFrame ns swap' left right rs).eval r) (.binary .compose x y)) :
    ∃ a b, r = .binary .compose a b := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  have hn' := accepted_expanded_results_numeric ns hf left right rs hp ha swap'
  apply (expandedFrame ns swap' left right rs).compose_form_of_paths r
    (expanded_handle_not_composition ns swap' left right rs hn') ?_ ?_ he
  · intro a b hr out hmatch
    subst r
    obtain ⟨_,_,_,number,hnum⟩ := accepted_expanded_minimum_decryption_match_numeric ns hf swap swap' left right rs hp ha
      a b hm hobs hmatch
    intro x y hv
    exact numeric_not_composition number x y (hnum.symm.trans hv)
  · intro f a hr hf' hv
    subst r
    obtain ⟨u,v,hpair⟩ := (accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha a
      (hm.subterm (.unary f .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega))).1.mpr hv
    exact (expanded_minimum_successful_projection_form ns swap left right rs hn ns.restricted f hf' a hm hpair).data_value ns swap' left right rs

end ExplainableCrypto.Helios.Symbolic.Historical.General
