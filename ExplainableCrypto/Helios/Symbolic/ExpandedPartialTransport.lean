import ExplainableCrypto.Helios.Symbolic.ExpandedValueOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A constructed partial cannot alias a published trustee partial even when
its arguments use arbitrary nested new-frame recipes. -/
theorem expanded_constructed_partial_not_trustee_partial (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b : Recipe (ExpandedHandles n))
    (ha : a.Public ns.restricted) (binding : Ground) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval (.binary .partialDecrypt a b))
      (.binary .partialDecrypt (.name ns.secretKey) binding) := by
  intro he
  exact (expanded_frame_opaque_protected ns swap left right rs hp).name_not_deducible a ha
    (by simp [Names.restricted]) ((EqE.partialDecrypt_iff _ _ _ _).mp he).1

/-- Constructed partials with minimum children are minimum. The only new
possible alias is a published slot, excluded by restricted-secret protection. -/
theorem expanded_minimum_partial_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .partialDecrypt a b) := by
  have hpub : (Term.binary .partialDecrypt a b).Public ns.restricted := ⟨ha.isPublic,hb.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpub
  rcases expanded_minimum_partial_decryption_form ns swap left right rs hn ns.restricted m hm he.symm with
    ⟨u,v,rfl⟩ | ⟨j,rfl⟩
  · have hargs := (EqE.partialDecrypt_iff _ _ _ _).mp he
    have hu := ha.least u hm.isPublic.1 hargs.1
    have hv := hb.least v hm.isPublic.2 hargs.2
    exact hm.of_equivalent_size hpub he (by simp only [Term.nodeCount]; omega)
  · exact False.elim (expanded_constructed_partial_not_trustee_partial ns swap left right rs hp a b ha.isPublic _
      (by simpa only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial] using he))

/-- Complete minimum partial-value equality branch in the accepted expanded
frame. Constructed arguments use smaller observations, mixed origins cannot
alias, and borrowed-slot comparisons transfer through the public tally recipes. -/
theorem expanded_minimum_partial_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s)
    {key binding key' binding' : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.binary .partialDecrypt key binding))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.binary .partialDecrypt key' binding'))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) := by
  rcases accepted_expanded_minimum_partial_form ns hf left right rs hp ha false r hr her with
    ⟨a,b,rfl⟩ | ⟨i,rfl⟩
  · rcases accepted_expanded_minimum_partial_form ns hf left right rs hp ha false s hs hes with
      ⟨c,d,rfl⟩ | ⟨j,rfl⟩
    · exact partial_decryption_equality_transfer _ _ a b c d hr.isPublic hs.isPublic hobs
    · have hneq (swap : Bool) : ¬ EqE ((expandedFrame ns swap left right rs).eval (.binary .partialDecrypt a b))
          ((expandedFrame ns swap left right rs).eval (.var (expandedPartial j))) := by
        simp only [Frame.eval,Term.subst,expanded_frame_partial]
        exact expanded_constructed_partial_not_trustee_partial ns swap left right rs hp a b hr.isPublic.1 _
      exact ⟨fun h => False.elim (hneq false h),fun h => False.elim (hneq true h)⟩
  · rcases accepted_expanded_minimum_partial_form ns hf left right rs hp ha false s hs hes with
      ⟨c,d,rfl⟩ | ⟨j,rfl⟩
    · have hneq (swap : Bool) : ¬ EqE ((expandedFrame ns swap left right rs).eval (.binary .partialDecrypt c d))
          ((expandedFrame ns swap left right rs).eval (.var (expandedPartial i))) := by
        simp only [Frame.eval,Term.subst,expanded_frame_partial]
        exact expanded_constructed_partial_not_trustee_partial ns swap left right rs hp c d hs.isPublic.1 _
      exact ⟨fun h => False.elim (hneq false h.symm),fun h => False.elim (hneq true h.symm)⟩
    · simpa only [Frame.eval,Term.subst,expanded_frame_partial] using
        tally_partial_equality_swap ns hf left right rs hp i j

end ExplainableCrypto.Helios.Symbolic.Historical.General
