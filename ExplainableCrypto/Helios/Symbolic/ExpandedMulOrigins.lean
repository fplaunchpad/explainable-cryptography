import ExplainableCrypto.Helios.Symbolic.MultiplicationOriginTools
import ExplainableCrypto.Helios.Symbolic.ExpandedDecryptionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulProjections

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Numerals cannot have multiplication values, whether fused or unfused. -/
theorem numeric_not_multiplication (number : Nat) (x y : Ground) :
    ¬ EqE (addNumeral number) (.binary .mul x y) := by
  cases number with
  | zero => exact fun he => mul_not_eqE_constant _ _ .zero he.symm
  | succ number => exact arithmetic_not_eqE_mul .add (Or.inl rfl) _ _ _ _

/-- No actual expanded handle can conceal a multiplication value. -/
theorem expanded_handle_not_multiplication (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n)) (x y : Ground) :
    ¬ EqE ((expandedFrame ns swap left right rs).value v) (.binary .mul x y) := by
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro he
    have hv : EqE ((frame ns swap left right).value old) (.binary .mul x y) := by
      simpa only [expandedFrame,Fin.addCases_left] using he
    fin_cases old
    · exact mul_not_eqE_pk _ _ _ hv.symm
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
      exact mul_not_eqE_passive_binary _ _ _ _ .pair (Or.inl rfl) (hv.symm.trans hp)
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
      exact mul_not_eqE_passive_binary _ _ _ _ .pair (Or.inl rfl) (hv.symm.trans hp)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro he
      have hv : EqE (tallyPartial ns swap left right rs j) (.binary .mul x y) := by
        simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using he
      exact mul_not_eqE_passive_binary _ _ _ _ .partialDecrypt (Or.inr rfl) hv.symm
    · intro he
      obtain ⟨number,hnum⟩ := hn j
      exact numeric_not_multiplication number x y (hnum.symm.trans
        (by simpa only [expandedFrame,Fin.addCases_right] using he))

/-- An irreducible product value at a source minimum forces exact raw mul syntax. -/
theorem expanded_minimum_normal_mul_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {x y : Ground} (ht : Irreducible (.binary .mul x y))
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .mul x y)) :
    ∃ a b, r = .binary .mul a b := by
  apply (expandedFrame ns swap left right rs).normal_mul_form_of_paths r
    (fun v x y _ => expanded_handle_not_multiplication ns swap left right rs hn v x y) ?_ ?_ ht he
  · intro a b hr out hmatch
    subst r
    exact False.elim (expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out hmatch)
  · intro f a hr hf hv
    obtain ⟨x,y,hpair⟩ := hv
    subst r
    exact (expanded_minimum_successful_projection_form ns swap left right rs hn restricted f hf a hm hpair).data_value ns swap left right rs

/-- Destination normal-product origins use only the original recipe-size
observation bound. Borrowed E6 success is excluded by its numeric output;
a larger result probe and destination minimum size are unnecessary. -/
theorem accepted_expanded_minimum_normal_mul_form_after_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount)
    {x y : Ground} (ht : Irreducible (.binary .mul x y))
    (he : EqE ((expandedFrame ns swap' left right rs).eval r) (.binary .mul x y)) :
    ∃ a b, r = .binary .mul a b := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  have hn' := accepted_expanded_results_numeric ns hf left right rs hp ha swap'
  apply (expandedFrame ns swap' left right rs).normal_mul_form_of_paths r
    (fun v x y _ => expanded_handle_not_multiplication ns swap' left right rs hn' v x y) ?_ ?_ ht he
  · intro a b hr out hmatch
    subst r
    obtain ⟨_,_,_,number,hnum⟩ := accepted_expanded_minimum_decryption_match_numeric ns hf swap swap' left right rs hp ha a b hm hobs hmatch
    intro x y _ he
    exact numeric_not_multiplication number x y (hnum.symm.trans he)
  · intro f a hr hf' hv
    subst r
    obtain ⟨u,v,hpair⟩ := (accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha a
      (hm.subterm (.unary f .hole)) (hobs.mono (by simp only [Term.nodeCount]; omega))).1.mpr hv
    exact (expanded_minimum_successful_projection_form ns swap left right rs hn ns.restricted f hf' a hm hpair).data_value ns swap' left right rs

/-- A non-ciphertext multiplication E-value forces exact raw mul syntax even
when the supplied product still contains reducible factors or fusion groups. -/
theorem expanded_minimum_non_ciphertext_mul_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {x y : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .mul x y))
    (hc : ¬ ((expandedFrame ns swap left right rs).eval r).CiphertextValue) :
    ∃ a b, r = .binary .mul a b := by
  obtain ⟨t,ht,hi⟩ := exists_normal_form (.binary .mul x y)
  rcases ht.sound.mul_irreducible_shape hi with ⟨u,v,rfl⟩ | ⟨k,nr,m,rfl⟩
  · exact expanded_minimum_normal_mul_form ns swap left right rs hn restricted r hm hi (he.trans ht.sound)
  · exact False.elim (hc ⟨k,nr,m,he.trans ht.sound⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General
