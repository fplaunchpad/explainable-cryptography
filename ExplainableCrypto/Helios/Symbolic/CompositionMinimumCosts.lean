import ExplainableCrypto.Helios.Symbolic.DestructorArithmeticTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- Exact syntax accounting: leaf sizes plus the number of leaves equal the
whole tree size plus one. Repeated occurrences each contribute their own cost. -/
theorem Term.composeLeaves_nodeCount (r : Term V) :
    (r.composeLeaves.map Term.nodeCount).sum + r.composeLeaves.card = r.nodeCount + 1 := by
  induction r with
  | binary f a b ia ib =>
    cases f <;> simp only [composeLeaves,Multiset.map_add,Multiset.sum_add,Multiset.card_add,
      Multiset.map_singleton,Multiset.sum_singleton,Multiset.card_singleton,Term.nodeCount]
    all_goals omega
  | _ => simp only [composeLeaves,Multiset.map_singleton,Multiset.sum_singleton,Multiset.card_singleton]

/-- Every outer composition leaf inherits minimum size from the whole recipe. -/
theorem MinimalRecipe.compose_leaf {r a : Term V} (hm : MinimalRecipe restricted σ r)
    (ha : a ∈ r.composeLeaves) : MinimalRecipe restricted σ a := by
  obtain ⟨⟨c,hc⟩,_⟩ := Term.composeLeaves_mem ha
  rw [← hc] at hm
  exact hm.subterm c

/-- Equal substituted full-E bags of minimum leaves have equal cost bags.
Both leaf minima are in the same source world; no observation transport occurs. -/
theorem minimum_leaf_cost_bags_eq (xs ys : Multiset (Term V))
    (hx : ∀ x ∈ xs, MinimalRecipe restricted σ x)
    (hy : ∀ y ∈ ys, MinimalRecipe restricted σ y)
    (he : xs.map (fun x => (x.subst σ).fullClass) = ys.map (fun y => (y.subst σ).fullClass)) :
    xs.map Term.nodeCount = ys.map Term.nodeCount := by
  rw [← Multiset.rel_eq,Multiset.rel_map] at he ⊢
  exact he.mono (fun x hxm y hym hxy => by
    have heq := (fullClass_eq_iff _ _).mp hxy
    exact Nat.le_antisymm ((hx x hxm).least y (hy y hym).isPublic heq)
      ((hy y hym).least x (hx x hxm).isPublic heq.symm))

/-- Equal leaf cost bags determine the exact whole composition-tree cost. -/
theorem Term.nodeCount_eq_of_compose_leaf_costs {r s : Term V}
    (he : r.composeLeaves.map Term.nodeCount = s.composeLeaves.map Term.nodeCount) :
    r.nodeCount = s.nodeCount := by
  have hsum := congrArg Multiset.sum he
  have hcard := congrArg Multiset.card he
  simp only [Multiset.card_map] at hcard
  have hr := r.composeLeaves_nodeCount
  have hs := s.composeLeaves_nodeCount
  omega

end ExplainableCrypto.Helios.Symbolic
