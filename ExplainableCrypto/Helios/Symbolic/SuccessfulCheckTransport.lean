import ExplainableCrypto.Helios.Symbolic.HonestCheckCombinations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Honest component checks succeed for every valid candidate substitution,
including nonliteral bit representations and either assignment. -/
theorem honest_component_check_recipe_valid (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (j : Fin (n+1)) :
    EqE ((frame ns swap left right).eval (.ternary .checkspk (.var 0)
      (combinationRecipe (.leaf (i,j))) ((Term.var i.succ).project (n+1+j.val)))) (.const .ok) := by
  have h := (honest_proofs_valid ns i (choice swap left right i).value (choice swap left right i).valid).2 j
  have hk : (frame ns swap left right).value 0 = publicKey ns := rfl
  simpa only [Frame.eval,Term.subst,Term.subst_project,frame_voter_handle,
    combinationRecipe,Combination.evaluate,hk] using h

/-- The aggregate uses the complete honest ciphertext combination. Its
success follows the full E0 candidate-sum condition, not raw normalization. -/
theorem honest_aggregate_check_recipe_valid (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) :
    EqE ((frame ns swap left right).eval (.ternary .checkspk (.var 0)
      (combinationRecipe (voterCombination (n := n) i)) ((Term.var i.succ).project (2*(n+1))))) (.const .ok) := by
  have h := (honest_proofs_valid ns i (choice swap left right i).value (choice swap left right i).valid).1
  have hk : (frame ns swap left right).value 0 = publicKey ns := rfl
  simpa only [voterCombination_recipe,Frame.eval,Term.subst,aggregateCiphertext_subst,
    Term.subst_project,frame_voter_handle,hk] using h

/-- Minimum proof origins exhaust constructed, honest component and honest
aggregate cases. Key and bound-ciphertext agreement remain explicit throughout. -/
theorem minimum_check_success_transfer (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (a b c : Recipe 3)
    (ha : a.Public ns.restricted)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hc : MinimalRecipe ns.restricted (frame ns swap left right).value c)
    (hobs : Frame.ObservationsBelow (frame ns swap left right) (frame ns swap' left right)
      (Term.ternary .checkspk a b c).nodeCount)
    (he : EqE ((frame ns swap left right).eval (.ternary .checkspk a b c)) (.const .ok)) :
    EqE ((frame ns swap' left right).eval (.ternary .checkspk a b c)) (.const .ok) := by
  obtain ⟨nr,bit,_,_,hproof⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have form := minimum_proof_form ns swap left right ns.restricted c hc hproof
  rcases form with ⟨k,r,m,d,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,rfl⟩
  · exact constructed_check_success_transfer _ _ a b k r m d ha hb.isPublic hc.isPublic hobs he
  · apply honest_check_success_transfer ns hf swap swap' left right a b _ ha hb (.leaf (i,j)) ?_
      (honest_component_check_recipe_valid ns swap' left right i j) hobs he
    exact ⟨.name (ns.nonce i j),(choice swap left right i).value j,
      (component_proof_recipe_value ns swap left right i j).trans
        (.spk (.refl _) (.refl _) (.refl _) (combination_value ns swap left right (.leaf (i,j))).symm)⟩
  · apply honest_check_success_transfer ns hf swap swap' left right a b _ ha hb (voterCombination i) ?_
      (honest_aggregate_check_recipe_valid ns swap' left right i) hobs he
    exact ⟨foldCandidates .compose (fun j => .name (ns.nonce i j)),
      foldCandidates .add (choice swap left right i).value,
      (aggregate_proof_recipe_value ns swap left right i).trans
        (.spk (.refl _) (.refl _) (.refl _) (voterCombination_value ns swap left right i).symm)⟩

/-- Every check with minimum children has a shared minimum under the two
strict smaller hypotheses of simultaneous induction. Successful checks share
the public one-node ok recipe; stuck checks are already minimum. -/
theorem minimum_children_check_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (a b c : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hc : MinimalRecipe ns.restricted (frame ns swap left right).value c)
    (hforward : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right)
      (Term.ternary .checkspk a b c).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right)
      (Term.ternary .checkspk a b c).nodeCount) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.ternary .checkspk a b c) := by
  classical
  by_cases hs : ProofCheckMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b)
      ((frame ns swap left right).eval c)
  · have he := hs.reduces.sound
    exact ⟨.const .ok,.of_nodeCount_one trivial rfl,he,
      minimum_check_success_transfer ns hf swap swap' left right a b c ha.isPublic hb hc
        (observationsBelow_of_two_way_minima ns hf swap swap' left right _ hforward hreverse) he⟩
  · exact .of_minimal (minimum_stuck_check_of_children ns swap left right a b c ha hb hc hs)

end ExplainableCrypto.Helios.Symbolic.Historical.General
