import ExplainableCrypto.Helios.Symbolic.CompositionMinimumCosts

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Minimum raw composition leaves are semantically indivisible in the source
frame. The caller's policy is arbitrary; no swapped-world premise is required. -/
theorem minimum_compose_leaves_atomic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hmin : ∀ a ∈ r.composeLeaves, MinimalRecipe restricted (frame ns swap left right).value a) :
    ∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE ((frame ns swap left right).eval a) (.binary .compose x y) := by
  intro a ha x y he
  obtain ⟨u,v,hu⟩ := minimum_compose_form ns swap left right restricted a (hmin a ha) he
  exact (Term.composeLeaves_mem ha).2 u v hu

/-- Minimum leaves force minimum total composition size. Source full-E factor
bags pair equal-value minimum leaves, whose equal costs fix the whole size. -/
theorem minimum_of_compose_leaves (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.composeLeaves, MinimalRecipe restricted (frame ns swap left right).value a) :
    MinimalRecipe restricted (frame ns swap left right).value r := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) r hp
  have hmr := minimum_compose_leaves_atomic ns swap left right restricted r hmin
  have hmm := minimum_compose_leaves_atomic ns swap left right restricted m (fun _ ha => hm.compose_leaf ha)
  have hr := Term.compose_leaves_substitution (frame ns swap left right).value r hmr
  have hs := Term.compose_leaves_substitution (frame ns swap left right).value m hmm
  have hbag := (eqE_iff_compose_value_factors _ _ hr.2 hs.2).mp he
  rw [hr.1,hs.1] at hbag
  have hcost := minimum_leaf_cost_bags_eq r.composeLeaves m.composeLeaves hmin
    (fun _ ha => hm.compose_leaf ha) hbag
  exact hm.of_equivalent_size hp he (Nat.le_of_eq (Term.nodeCount_eq_of_compose_leaf_costs hcost))

/-- Composition preserves minimum size when both children are minimum. This
holds under any caller name policy in the actual initial historical frame. -/
theorem minimum_compose_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (a b : Recipe 3)
    (ha : MinimalRecipe restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe restricted (frame ns swap left right).value b) :
    MinimalRecipe restricted (frame ns swap left right).value (.binary .compose a b) := by
  apply minimum_of_compose_leaves ns swap left right restricted (.binary .compose a b) ⟨ha.isPublic,hb.isPublic⟩
  intro x hx
  rcases Multiset.mem_add.mp hx with hxa | hxb
  · exact ha.compose_leaf hxa
  · exact hb.compose_leaf hxb

end ExplainableCrypto.Helios.Symbolic.Historical.General
