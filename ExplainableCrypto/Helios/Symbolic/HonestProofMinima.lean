import ExplainableCrypto.Helios.Symbolic.RemainingRootTransport

namespace ExplainableCrypto.Helios.Symbolic

theorem Term.drop_nodeCount {V : Type} (t : Term V) (k : Nat) :
    (t.drop k).nodeCount = t.nodeCount + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Term.drop_succ_outer]; simp only [Term.nodeCount, ih]; omega

theorem Term.project_nodeCount {V : Type} (t : Term V) (k : Nat) :
    (t.project k).nodeCount = t.nodeCount + k + 1 := by
  simp only [Term.project, Term.nodeCount, Term.drop_nodeCount]
  omega

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every honest component proof selector attains its exact indexed syntax
minimum. Freshness prevents a shorter component selector with the same nonce. -/
theorem minimum_component_proof_selector (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (j : Fin (n+1)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value
      ((Term.var i.succ).project (n+1+j.val)) := by
  have hp := (ProjectionChain.project i.succ (n+1+j.val)).isPublic ns.restricted
  have hv := component_proof_recipe_value ns swap left right i j
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  rcases minimum_proof_form ns swap left right ns.restricted m hm (he.symm.trans hv) with
    ⟨a,b,c,d,rfl⟩ | ⟨k,l,rfl⟩ | ⟨k,rfl⟩
  · have hn := hm.isPublic.2.1.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
    exact False.elim (constructed_proof_not_component ns swap left right a b c d hn i j (he.symm.trans hv))
  · have hi := (component_proof_equality_iff ns hf swap left right i k j l).mp
      (hv.symm.trans (he.trans (component_proof_recipe_value ns swap left right k l)))
    have hval := congrArg Fin.val hi.2
    exact hm.of_equivalent_size hp he (by simp only [Term.project_nodeCount, Term.nodeCount]; omega)
  · exact hm.of_equivalent_size hp he (by
      have := j.isLt
      simp only [Term.project_nodeCount, Term.nodeCount]
      omega)

/-- With at least two candidates, aggregate proofs cannot alias a component;
all remaining honest aggregate selectors have the same indexed size. -/
theorem minimum_aggregate_proof_selector (ns : Names n) (hf : ns.Fresh) (hn : n ≠ 0) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) :
    MinimalRecipe ns.restricted (frame ns swap left right).value
      ((Term.var i.succ).project (2*(n+1))) := by
  have hp := (ProjectionChain.project i.succ (2*(n+1))).isPublic ns.restricted
  have hv := aggregate_proof_recipe_value ns swap left right i
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  rcases minimum_proof_form ns swap left right ns.restricted m hm (he.symm.trans hv) with
    ⟨a,b,c,d,rfl⟩ | ⟨k,l,rfl⟩ | ⟨k,rfl⟩
  · have hnonce := hm.isPublic.2.1.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
    exact False.elim (constructed_proof_not_aggregate ns swap left right a b c d hnonce i (he.symm.trans hv))
  · have hi := (component_aggregate_proof_equality_iff ns hf swap left right k i l).mp
      ((component_proof_recipe_value ns swap left right k l).symm.trans (he.symm.trans hv))
    exact False.elim (hn hi.1)
  · exact hm.of_equivalent_size hp he (by simp only [Term.project_nodeCount, Term.nodeCount]; omega)

/-- At one candidate, use the shorter component selector; otherwise the
aggregate selector is already minimum. The same witness works in both worlds. -/
theorem aggregate_selector_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right)
      ((Term.var i.succ).project (2*(n+1))) := by
  by_cases hn : n = 0
  · have value (s : Bool) :
        EqE ((frame ns s left right).eval ((Term.var i.succ).project (2*(n+1))))
          ((frame ns s left right).eval ((Term.var i.succ).project (n+1+(0 : Fin (n+1)).val))) :=
      (aggregate_proof_recipe_value ns s left right i).trans
        (((component_aggregate_proof_equality_iff ns hf s left right i i 0).mpr ⟨hn,rfl⟩).symm.trans
          (component_proof_recipe_value ns s left right i 0).symm)
    exact ⟨_, minimum_component_proof_selector ns hf swap left right i 0, value swap, value swap'⟩
  · exact .of_minimal (minimum_aggregate_proof_selector ns hf hn swap left right i)

end ExplainableCrypto.Helios.Symbolic.Historical.General
