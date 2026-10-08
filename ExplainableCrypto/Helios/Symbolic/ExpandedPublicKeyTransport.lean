import ExplainableCrypto.Helios.Symbolic.ExpandedPublicKeyOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem expanded_election_handle_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    (expandedFrame ns swap left right rs).eval (.var (expandedOld 0)) = publicKey ns := by
  rw [Frame.eval,Term.subst,expanded_frame_old]
  rfl

/-- The full public-name policy prevents constructed keys from aliasing the
retained election key, including arguments that use new partial/result handles. -/
theorem expanded_constructed_key_not_election_key (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a : Recipe (ExpandedHandles n)) (ha : a.Public ns.restricted) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval (.unary .pk a)) (publicKey ns) := by
  intro he
  exact (expanded_frame_opaque_protected ns swap left right rs hp).name_not_deducible a ha
    (by simp [Names.restricted]) ((EqE.pk_iff _ _).mp he)

theorem expanded_minimum_election_key_handle (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (publicKey ns)) : r = .var (expandedOld 0) := by
  rcases expanded_minimum_public_key_form ns swap left right rs hn ns.restricted r hm he with hr | ⟨a,rfl⟩
  · exact hr
  · exact False.elim (expanded_constructed_key_not_election_key ns swap left right rs hp a hm.isPublic he)

/-- A minimum public argument yields a minimum pk constructor. The only
possible borrowed alias is excluded by secret-name non-deducibility. -/
theorem expanded_minimum_pk_of_child (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a : Recipe (ExpandedHandles n)) (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.unary .pk a) := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) (.unary .pk a) ha.isPublic
  rcases expanded_minimum_public_key_form ns swap left right rs hn ns.restricted m hm he.symm with rfl | ⟨b,rfl⟩
  · have hval : EqE ((expandedFrame ns swap left right rs).eval (.unary .pk a))
        ((expandedFrame ns swap left right rs).eval (.var (expandedOld 0))) := he
    rw [expanded_election_handle_value] at hval
    exact False.elim (expanded_constructed_key_not_election_key ns swap left right rs hp a ha.isPublic hval)
  · have hle := ha.least b hm.isPublic ((EqE.pk_iff _ _).mp he)
    exact hm.of_equivalent_size ha.isPublic he (by simp only [Term.nodeCount]; omega)

/-- All four key-form comparisons: equal retained handles, two excluded mixed
aliases, and constructed keys reduced to strictly smaller argument equality. -/
theorem expanded_key_form_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (r s : Recipe (ExpandedHandles n))
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted)
    (hfr : ExpandedPublicKeyRecipeForm r) (hfs : ExpandedPublicKeyRecipeForm s)
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) := by
  have mixed (swap : Bool) (a : Recipe (ExpandedHandles n)) (ha : a.Public ns.restricted) :
      ¬ EqE ((expandedFrame ns swap left right rs).eval (.unary .pk a))
        ((expandedFrame ns swap left right rs).eval (.var (expandedOld 0))) := by
    rw [expanded_election_handle_value]
    exact expanded_constructed_key_not_election_key ns swap left right rs hp a ha
  rcases hfr with rfl | ⟨a,rfl⟩
  · rcases hfs with rfl | ⟨b,rfl⟩
    · exact ⟨fun _ => .refl _,fun _ => .refl _⟩
    · exact iff_of_false (fun he => mixed false b hs he.symm) (fun he => mixed true b hs he.symm)
  · rcases hfs with rfl | ⟨b,rfl⟩
    · exact iff_of_false (mixed false a hr) (mixed true a hr)
    · have h := hobs a b hr hs (by simp only [Term.nodeCount]; omega)
      exact (EqE.pk_iff _ _).trans (h.trans (EqE.pk_iff _ _).symm)

/-- The complete minimum key-value equality branch. Numeric values are needed
only in the source world to classify its minimum recipes. -/
theorem expanded_minimum_public_key_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns false left right rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s) {key key' : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.unary .pk key))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.unary .pk key'))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_key_form_equality_swap ns left right rs hp r s hr.isPublic hs.isPublic
    (expanded_minimum_public_key_form ns false left right rs hn ns.restricted r hr her)
    (expanded_minimum_public_key_form ns false left right rs hn ns.restricted s hs hes) hobs

/-- The accepted-election interface discharges the auxiliary numeric premise;
only the intended smaller-observation induction hypothesis remains. -/
theorem accepted_expanded_minimum_public_key_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s) {key key' : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.unary .pk key))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.unary .pk key'))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_minimum_public_key_equality_swap ns left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp ha false) r s hr hs her hes hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
