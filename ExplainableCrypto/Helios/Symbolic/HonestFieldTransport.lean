import ExplainableCrypto.Helios.Symbolic.CompleteProjectionTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum recipe matching an honest component proof preserves that match
in any assignment. Nonce provenance also covers the one-candidate aggregate alias. -/
theorem minimum_component_match_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (i : Fin 2) (j : Fin (n+1))
    (he : EqE ((frame ns swap left right).eval r) (componentProof ns i (choice swap left right i).value j)) :
    EqE ((frame ns swap' left right).eval r) (componentProof ns i (choice swap' left right i).value j) := by
  rcases minimum_proof_form ns swap left right ns.restricted r hm he with
    ⟨a,b,c,d,rfl⟩ | ⟨k,l,rfl⟩ | ⟨k,rfl⟩
  · exact False.elim (constructed_proof_not_component ns swap left right a b c d
      (hm.isPublic.2.1.of_subset (fun _ h => Finset.mem_union_right _ h)) i j he)
  · have hi := (component_proof_equality_iff ns hf swap left right k i l j).mp
      ((component_proof_recipe_value ns swap left right k l).symm.trans he)
    exact (component_proof_recipe_value ns swap' left right k l).trans
      ((component_proof_equality_iff ns hf swap' left right k i l j).mpr hi)
  · have hi := (component_aggregate_proof_equality_iff ns hf swap left right i k j).mp
      (he.symm.trans (aggregate_proof_recipe_value ns swap left right k))
    exact (aggregate_proof_recipe_value ns swap' left right k).trans
      ((component_aggregate_proof_equality_iff ns hf swap' left right i k j).mpr hi).symm

/-- The same matching transfer for aggregate proofs, retaining the component
alias when there is exactly one candidate. -/
theorem minimum_aggregate_match_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r) (i : Fin 2)
    (he : EqE ((frame ns swap left right).eval r) (aggregateProof ns i (choice swap left right i).value)) :
    EqE ((frame ns swap' left right).eval r) (aggregateProof ns i (choice swap' left right i).value) := by
  rcases minimum_proof_form ns swap left right ns.restricted r hm he with
    ⟨a,b,c,d,rfl⟩ | ⟨k,l,rfl⟩ | ⟨k,rfl⟩
  · exact False.elim (constructed_proof_not_aggregate ns swap left right a b c d
      (hm.isPublic.2.1.of_subset (fun _ h => Finset.mem_union_right _ h)) i he)
  · have hi := (component_aggregate_proof_equality_iff ns hf swap left right k i l).mp
      ((component_proof_recipe_value ns swap left right k l).symm.trans he)
    exact (component_proof_recipe_value ns swap' left right k l).trans
      ((component_aggregate_proof_equality_iff ns hf swap' left right k i l).mpr hi)
  · have hi := (aggregate_proof_equality_iff ns hf swap left right k i).mp
      ((aggregate_proof_recipe_value ns swap left right k).symm.trans he)
    exact (aggregate_proof_recipe_value ns swap' left right k).trans
      ((aggregate_proof_equality_iff ns hf swap' left right k i).mpr hi)

/-- Matching any honest field by a minimum recipe transfers without a smaller
observation premise. The field's indexed recipe need not itself be minimum. -/
theorem minimum_honest_field_match_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (i : Fin 2) (k : Nat) (hk : k < fieldCount n)
    (he : EqE ((frame ns swap left right).eval r)
      ((frame ns swap left right).eval ((Term.var i.succ).project k))) :
    EqE ((frame ns swap' left right).eval r)
      ((frame ns swap' left right).eval ((Term.var i.succ).project k)) := by
  have hlen : k < (ballotFields ns i (choice swap left right i).value).length := by
    simpa only [ballot_fields_length] using hk
  rcases ballot_field_cases ns i (choice swap left right i).value k hlen with
    ⟨j,rfl,_⟩ | ⟨j,rfl,_⟩ | ⟨rfl,_⟩
  · have hr := minimum_honest_ciphertext_origin ns hf swap left right r hm i j
      (he.trans (combination_value ns swap left right (.leaf (i,j))))
    rw [hr]
    exact .refl _
  · exact (minimum_component_match_transfer ns hf swap swap' left right r hm i j
      (he.trans (component_proof_recipe_value ns swap left right i j))).trans
      (component_proof_recipe_value ns swap' left right i j).symm
  · exact (minimum_aggregate_match_transfer ns hf swap swap' left right r hm i
      (he.trans (aggregate_proof_recipe_value ns swap left right i))).trans
      (aggregate_proof_recipe_value ns swap' left right i).symm

/-- Every public representative of field k has at least k+1 nodes. The weaker
uniform bound includes the shorter one-candidate aggregate representative. -/
theorem honest_field_public_size_bound (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) (hp : r.Public ns.restricted)
    (i : Fin 2) (k : Nat) (hk : k < fieldCount n)
    (he : EqE ((frame ns swap left right).eval r)
      ((frame ns swap left right).eval ((Term.var i.succ).project k))) : k+1 ≤ r.nodeCount := by
  have hlen : k < (ballotFields ns i (choice swap left right i).value).length := by
    simpa only [ballot_fields_length] using hk
  rcases ballot_field_cases ns i (choice swap left right i).value k hlen with
    ⟨j,rfl,_⟩ | ⟨j,rfl,_⟩ | ⟨rfl,_⟩
  · have hle := (minimum_ciphertext_selector ns hf swap left right i j).least r hp he.symm
    simp only [Term.project_nodeCount, Term.nodeCount] at hle
    omega
  · have hle := (minimum_component_proof_selector ns hf swap left right i j).least r hp he.symm
    simp only [Term.project_nodeCount, Term.nodeCount] at hle
    omega
  · by_cases hn : n = 0
    · have hc := (component_proof_recipe_value ns swap left right i 0).trans
        (((component_aggregate_proof_equality_iff ns hf swap left right i i 0).mpr ⟨hn,rfl⟩).trans
          (aggregate_proof_recipe_value ns swap left right i).symm)
      have hle := (minimum_component_proof_selector ns hf swap left right i 0).least r hp (hc.trans he.symm)
      simp only [Term.project_nodeCount, Term.nodeCount, Fin.val_zero] at hle
      omega
    · have hle := (minimum_aggregate_proof_selector ns hf hn swap left right i).least r hp he.symm
      simp only [Term.project_nodeCount, Term.nodeCount] at hle
      omega

end ExplainableCrypto.Helios.Symbolic.Historical.General
