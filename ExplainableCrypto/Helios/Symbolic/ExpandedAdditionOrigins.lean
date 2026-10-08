import ExplainableCrypto.Helios.Symbolic.AdditionOriginTools
import ExplainableCrypto.Helios.Symbolic.ExpandedDecryptionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulProjections

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Published results are additional size-one origins of numeric addition values. -/
def ExpandedAdditionRecipeForm (r : Recipe (ExpandedHandles n)) : Prop :=
  ((∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one) ∨
  ∃ j, r = .var (expandedResult j)

/-- Only result handles can have additive values in the actual expanded frame. -/
theorem expanded_handle_addition_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (v : Fin (ExpandedHandles n)) {x y : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).value v) (.binary .add x y)) :
    ∃ j, v = expandedResult j := by
  revert he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro he
    have hv : EqE ((frame ns swap left right).value old) (.binary .add x y) := by
      simpa only [expandedFrame, Fin.addCases_left] using he
    fin_cases old
    · exact False.elim (arithmetic_not_eqE_pk .add (Or.inl rfl) _ _ _ hv.symm)
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
      exact False.elim (arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp))
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
      exact False.elim (arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp))
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro he
      have hv : EqE (tallyPartial ns swap left right rs j) (.binary .add x y) := by
        simpa only [expandedFrame, Fin.addCases_right, Fin.addCases_left] using he
      exact False.elim (arithmetic_not_eqE_passive_binary .add .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _ hv.symm)
    · exact fun _ => ⟨j, rfl⟩

/-- Source-minimum addition values include numeric result handles. -/
theorem expanded_minimum_add_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {x y : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .add x y)) :
    ExpandedAdditionRecipeForm r := by
  apply (expandedFrame ns swap left right rs).add_form_of_paths r
    (fun r => ∃ j, r = .var (expandedResult j)) ?_ ?_ ?_ he
  · intro v x y hv
    obtain ⟨j,rfl⟩ := expanded_handle_addition_origin ns swap left right rs v hv
    exact ⟨j,rfl⟩
  · intro a b hr out hmatch
    subst r
    exact expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out hmatch
  · intro f a hr hf hv
    obtain ⟨x,y,hpair⟩ := hv
    subst r
    exact (expanded_minimum_successful_projection_form ns swap left right rs hn restricted f hf a hm hpair).data_value ns swap left right rs

/-- Destination origins require the bound that admits the published-result
probe. The source recipe alone is assumed minimum. -/
theorem accepted_expanded_minimum_add_form_after_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) (r.nodeCount + 2))
    {x y : Ground} (he : EqE ((expandedFrame ns swap' left right rs).eval r) (.binary .add x y)) :
    ExpandedAdditionRecipeForm r := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  apply (expandedFrame ns swap' left right rs).add_form_of_paths r
    (fun r => ∃ j, r = .var (expandedResult j)) ?_ ?_ ?_ he
  · intro v x y hv
    obtain ⟨j,rfl⟩ := expanded_handle_addition_origin ns swap' left right rs v hv
    exact ⟨j,rfl⟩
  · intro a b hr
    subst r
    exact accepted_expanded_minimum_decryption_failure_with_result_probe ns hf swap swap' left right rs hp ha a b hm hobs
  · intro f a hr hf' hv
    subst r
    obtain ⟨u,v,hpair⟩ := (accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha a
      (hm.subterm (.unary f .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega))).1.mpr hv
    exact (expanded_minimum_successful_projection_form ns swap left right rs hn ns.restricted f hf' a hm hpair).data_value ns swap' left right rs

end ExplainableCrypto.Helios.Symbolic.Historical.General
