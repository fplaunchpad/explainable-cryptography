import ExplainableCrypto.Helios.Symbolic.HonestProofMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every nonempty proof-only ballot suffix is minimum. A constructed pair must
pay for its first honest proof field; a tail alias has the same position. -/
theorem minimum_proof_tail (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (k : Nat)
    (hproof : n+1 ≤ k) (hk : k < fieldCount n) :
    MinimalRecipe ns.restricted (frame ns swap left right).value ((Term.var i.succ).drop k) := by
  have hp := (ProjectionChain.drop i.succ k).isPublic ns.restricted
  obtain ⟨x,y,hvalue⟩ := ballot_tail_pair_value ns swap left right i k hk
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  rcases minimum_pair_observation_form ns swap left right ns.restricted m hm (he.symm.trans hvalue) with
    ⟨u,v,rfl⟩ | ⟨j,l,hl,rfl⟩
  · have hfield : EqE ((frame ns swap left right).eval ((Term.var i.succ).project k))
        ((frame ns swap left right).eval u) :=
      (EqE.unary .fst he).trans (RootStep.fst _ _).sound
    have hlen : k < (ballotFields ns i (choice swap left right i).value).length := by
      simpa only [ballot_fields_length] using hk
    rcases ballot_field_cases ns i (choice swap left right i).value k hlen with
      ⟨j,hj,_⟩ | ⟨j,rfl,_⟩ | ⟨rfl,_⟩
    · have := j.isLt
      omega
    · have hle := (minimum_component_proof_selector ns hf swap left right i j).least u hm.isPublic.1 hfield
      exact hm.of_equivalent_size hp he (by
        simp only [Term.drop_nodeCount, Term.project_nodeCount, Term.nodeCount] at hle ⊢
        omega)
    · by_cases hn : n = 0
      · have hc : EqE ((frame ns swap left right).eval ((Term.var i.succ).project (n+1+(0 : Fin (n+1)).val)))
            ((frame ns swap left right).eval ((Term.var i.succ).project (2*(n+1)))) :=
          (component_proof_recipe_value ns swap left right i 0).trans
            (((component_aggregate_proof_equality_iff ns hf swap left right i i 0).mpr ⟨hn,rfl⟩).trans
              (aggregate_proof_recipe_value ns swap left right i).symm)
        have hle := (minimum_component_proof_selector ns hf swap left right i 0).least u hm.isPublic.1 (hc.trans hfield)
        exact hm.of_equivalent_size hp he (by
          simp only [Term.drop_nodeCount, Term.project_nodeCount, Term.nodeCount, Fin.val_zero] at hle ⊢
          omega)
      · have hle := (minimum_aggregate_proof_selector ns hf hn swap left right i).least u hm.isPublic.1 hfield
        exact hm.of_equivalent_size hp he (by
          simp only [Term.drop_nodeCount, Term.project_nodeCount, Term.nodeCount] at hle ⊢
          omega)
  · have hpos := ((ballot_tail_equality_iff ns hf swap left right i j k l hk hl).mp he).2
    exact hm.of_equivalent_size hp he (by simp only [Term.drop_nodeCount, Term.nodeCount]; omega)

/-- Proof-only suffixes, including the empty suffix, have shared minima in both
worlds. The empty suffix uses bottom rather than claiming its raw chain minimum. -/
theorem proof_tail_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (k : Nat)
    (hproof : n+1 ≤ k) (hk : k ≤ fieldCount n) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) ((Term.var i.succ).drop k) := by
  by_cases hnonempty : k < fieldCount n
  · exact .of_minimal (minimum_proof_tail ns hf swap left right i k hproof hnonempty)
  · have heq : k = fieldCount n := by omega
    have value (s : Bool) :
        EqE ((frame ns s left right).eval ((Term.var i.succ).drop k)) (.const .bottom) := by
      have hv := ballot_tail_recipe_value ns s left right i k hk
      have hlen : (ballotFields ns i (choice s left right i).value).length ≤ k := by
        rw [ballot_fields_length]; omega
      simpa only [List.drop_eq_nil_of_le hlen, Term.tuple] using hv
    exact ⟨.const .bottom, .of_nodeCount_one trivial rfl, value swap, value swap'⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
