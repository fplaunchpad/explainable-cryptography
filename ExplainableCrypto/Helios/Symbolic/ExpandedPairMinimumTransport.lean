import ExplainableCrypto.Helios.Symbolic.ExpandedHonestTailMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedStuckOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every fst/snd of a source-minimum child has a shared expanded minimum.
Constructed pairs project to their minimum children; borrowed fields/tails use
old-data origins; stuck projections retain their original minimum syntax. -/
theorem expanded_minimum_child_projection_shared (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (f : Unary) (hproj : f=.fst ∨ f=.snd) (a : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.unary f a) := by
  classical
  by_cases hpair : ((expandedFrame ns swap left right rs).eval a).PairValue
  · obtain ⟨x,y,he⟩ := hpair
    rcases expanded_minimum_pair_observation_form ns swap left right rs hn ns.restricted a hm he with
      ⟨u,v,rfl⟩ | ⟨i,k,hk,rfl⟩
    · exact .projection_of_minimum_pair u v hm f hproj
    · rcases hproj with rfl | rfl
      · exact expanded_honest_field_shared_minimum ns hf swap swap' left right rs hp hn i k hk
      · simpa only [Term.drop_succ_outer] using
          expanded_ballot_tail_shared_minimum ns hf swap swap' left right rs hp hn i (k+1) (by omega)
  · exact .of_minimal (expanded_minimum_stuck_projection_of_child ns swap left right rs hn ns.restricted f hproj a hm
      (fun x y he => hpair ⟨x,y,he⟩))

/-- Accepted publication supplies the numeric source premise for both selectors. -/
theorem accepted_expanded_minimum_child_projection_shared (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (f : Unary) (hproj : f=.fst ∨ f=.snd) (a : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.unary f a) :=
  expanded_minimum_child_projection_shared ns hf swap swap' left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) f hproj a hm

/-- Pairs of minimum children have shared minima. An explicit minimum
competitor proves the original pair minimum; a borrowed tail competitor uses
unconditional honest field/tail match transfer in both assignments. -/
theorem accepted_expanded_minimum_children_pair_shared (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.binary .pair a b) := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp haccept swap
  have hpublic : (Term.binary .pair a b).Public ns.restricted := ⟨ha.isPublic,hb.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpublic
  rcases expanded_minimum_pair_observation_form ns swap left right rs hn ns.restricted m hm he.symm with
    ⟨u,v,rfl⟩ | ⟨i,k,hk,rfl⟩
  · have hargs := (EqE.pair_iff _ _ _ _).mp he
    have hu := ha.least u hm.isPublic.1 hargs.1
    have hv := hb.least v hm.isPublic.2 hargs.2
    exact .of_minimal (hm.of_equivalent_size hpublic he (by simp only [Term.nodeCount]; omega))
  · have hargs := (pair_equality_iff_projections _ _ _ (expanded_ballot_tail_pair_value ns swap left right rs i k hk)).mp he
    have hfirst := expanded_minimum_honest_field_match_transfer ns hf swap swap' left right rs hp hn a ha i k hk hargs.1
    have hrest := accepted_expanded_minimum_honest_tail_match_transfer ns hf swap swap' left right rs hp haccept b hb i (k+1) (by omega)
      (by simpa only [Term.drop_succ_outer,Frame.eval,Term.subst] using hargs.2)
    refine ⟨_,hm,he,?_⟩
    apply (pair_equality_iff_projections _ _ _ (expanded_ballot_tail_pair_value ns swap' left right rs i k hk)).mpr
    exact ⟨hfirst,by simpa only [Term.drop_succ_outer,Frame.eval,Term.subst] using hrest⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
