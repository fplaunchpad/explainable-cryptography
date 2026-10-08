import ExplainableCrypto.Helios.Symbolic.ExpandedCompositionOrigins
import ExplainableCrypto.Helios.Symbolic.CompositionObservationInduction
import ExplainableCrypto.Helios.Symbolic.CompositionMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Minimum raw leaves cannot hide further source composition values. -/
theorem expanded_minimum_compose_leaves_atomic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hmin : ∀ a ∈ r.composeLeaves, MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    ∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).eval a) (.binary .compose x y) := by
  intro a ha x y he
  obtain ⟨u,v,hu⟩ := expanded_minimum_compose_form ns swap left right rs hn restricted a (hmin a ha) he
  exact (Term.composeLeaves_mem ha).2 u v hu

/-- Existing full-E factor bags and leaf-cost equality force minimum total
composition size. Every repeated occurrence contributes its original cost. -/
theorem expanded_minimum_of_compose_leaves (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.composeLeaves, MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value r := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) r hp
  have hmr := expanded_minimum_compose_leaves_atomic ns swap left right rs hn restricted r hmin
  have hmm := expanded_minimum_compose_leaves_atomic ns swap left right rs hn restricted m (fun _ ha => hm.compose_leaf ha)
  have hr := Term.compose_leaves_substitution (expandedFrame ns swap left right rs).value r hmr
  have hs := Term.compose_leaves_substitution (expandedFrame ns swap left right rs).value m hmm
  have hbag := (eqE_iff_compose_value_factors _ _ hr.2 hs.2).mp he
  rw [hr.1,hs.1] at hbag
  have hcost := minimum_leaf_cost_bags_eq r.composeLeaves m.composeLeaves hmin
    (fun _ ha => hm.compose_leaf ha) hbag
  exact hm.of_equivalent_size hp he (Nat.le_of_eq (Term.nodeCount_eq_of_compose_leaf_costs hcost))

/-- Composition of minimum children is minimum under the caller's policy. -/
theorem expanded_minimum_compose_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe restricted (expandedFrame ns swap left right rs).value b) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.binary .compose a b) := by
  apply expanded_minimum_of_compose_leaves ns swap left right rs hn restricted (.binary .compose a b) ⟨ha.isPublic,hb.isPublic⟩
  intro x hx
  rcases Multiset.mem_add.mp hx with hxa | hxb
  · exact ha.compose_leaf hxa
  · exact hb.compose_leaf hxb

/-- Source and destination raw leaves are semantic composition atoms. The
existing subterm bounds pay for each after-swap origin test. -/
theorem accepted_expanded_minimum_compose_leaf_values (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount) :
    (∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).eval a) (.binary .compose x y)) ∧
    (∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE ((expandedFrame ns swap' left right rs).eval a) (.binary .compose x y)) := by
  refine ⟨expanded_minimum_compose_leaves_atomic ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted r (fun _ ha => hm.compose_leaf ha),?_⟩
  intro a hleaf x y he
  obtain ⟨⟨c,hc⟩,hraw⟩ := Term.composeLeaves_mem hleaf
  have hsize := c.nodeCount_hole_le a
  rw [hc] at hsize
  obtain ⟨u,v,hu⟩ := accepted_expanded_minimum_compose_form_after_swap ns hf swap swap' left right rs hp ha
    a (hm.compose_leaf hleaf) (hobs.mono hsize) he
  exact hraw u v hu

/-- Complete composition-valued equality branch for actual accepted expanded
frames. Existing full-E factor bags reduce it to strictly smaller public leaf
comparisons, retaining multiplicity and all candidate/handle parameters. -/
theorem accepted_expanded_minimum_composition_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    {x y u v : Ground}
    (her : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .compose x y))
    (hes : EqE ((expandedFrame ns swap left right rs).eval s) (.binary .compose u v))
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s) ↔
      EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) := by
  have har := accepted_expanded_minimum_compose_leaf_values ns hf swap swap' left right rs hp ha r hr (hobs.mono (by omega))
  have has := accepted_expanded_minimum_compose_leaf_values ns hf swap swap' left right rs hp ha s hs (hobs.mono (by omega))
  have hrf := Term.compose_leaves_substitution (expandedFrame ns swap left right rs).value r har.1
  have hsf := Term.compose_leaves_substitution (expandedFrame ns swap left right rs).value s has.1
  have hrt := Term.compose_leaves_substitution (expandedFrame ns swap' left right rs).value r har.2
  have hst := Term.compose_leaves_substitution (expandedFrame ns swap' left right rs).value s has.2
  have hsource := eqE_iff_compose_value_factors _ _ hrf.2 hsf.2
  have htarget := eqE_iff_compose_value_factors _ _ hrt.2 hst.2
  rw [hrf.1,hsf.1] at hsource
  rw [hrt.1,hst.1] at htarget
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  obtain ⟨a,b,rfl⟩ := expanded_minimum_compose_form ns swap left right rs hn ns.restricted r hr her
  obtain ⟨c,d,rfl⟩ := expanded_minimum_compose_form ns swap left right rs hn ns.restricted s hs hes
  exact hsource.trans ((composition_leaf_bag_transfer _ _ a b c d hr.isPublic hs.isPublic hobs).trans htarget.symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
