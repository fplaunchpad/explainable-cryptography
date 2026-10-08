import ExplainableCrypto.Helios.Symbolic.TrusteeFreeMinimumSupport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum complete tally binding has an exact old-plus-results syntax.
This excludes partial handles in every nested position, without erasing numerals
or asserting that their realization preserves minimum size. -/
theorem expanded_minimum_tally_result_support (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (b : Recipe (ExpandedHandles n)) (j : Fin (n+1))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (he : EqE ((expandedFrame ns swap left right rs).eval b) (tallyCiphertext ns swap left right rs j)) :
    ∃ r : Recipe (ResultHandles n), b = r.subst (fun i => .var (resultEmbedding i)) :=
  expanded_minimum_trustee_free_support ns swap left right rs hn ns.restricted b hm
    ((initial_recipe_trustee_free ns swap left right (tallyRecipe rs j)
      (tallyRecipe_public rs j ns.restricted hp)).of_eq he.symm)

/-- Complete E6 binding transport, with no remaining local-induction callback. -/
theorem accepted_expanded_trustee_binding (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    ExpandedTrusteeBindingTransport ns swap swap' left right rs := by
  apply accepted_expanded_trustee_binding_of_remaining_recipes ns hf swap swap' left right rs hp haccept
  intro j b hm hno he _ _
  exact False.elim (hno (expanded_minimum_tally_result_support ns swap left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) b j hm he))

/-- All public equality observations agree after every accepted public submission
and publication of all aggregate trustee partials and numeric results. -/
theorem accepted_expanded_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) :=
  accepted_expanded_staticEq_of_trustee_binding ns hf left right rs hp haccept
    (accepted_expanded_trustee_binding ns hf false true left right rs hp haccept)
    (accepted_expanded_trustee_binding ns hf true false left right rs hp haccept)

/-- The actual four-handle frame, including the tuple of aggregate partials. -/
theorem accepted_partial_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) :=
  accepted_partial_staticEq_of_trustee_binding ns hf left right rs hp haccept
    (accepted_expanded_trustee_binding ns hf false true left right rs hp haccept)
    (accepted_expanded_trustee_binding ns hf true false left right rs hp haccept)

/-- B8: the actual five-handle final transcript is statically equivalent for
fresh names and arbitrary valid ground candidates after an accepted public
submission sequence. Process transitions and labelled bisimilarity are separate. -/
theorem accepted_final_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) :=
  accepted_final_staticEq_of_trustee_binding ns hf left right rs hp haccept
    (accepted_expanded_trustee_binding ns hf false true left right rs hp haccept)
    (accepted_expanded_trustee_binding ns hf true false left right rs hp haccept)

end ExplainableCrypto.Helios.Symbolic.Historical.General
