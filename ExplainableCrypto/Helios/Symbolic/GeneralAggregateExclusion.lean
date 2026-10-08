import ExplainableCrypto.Helios.Symbolic.GeneralAcceptedProofs

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The whole nonce fold inherits a protected factor from one component's
honest aggregate value, even with arbitrary candidate representatives. -/
theorem frame_nonce_fold_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (rs : Fin (n + 1) → Ground) (j : Fin (n + 1)) (i : Fin 2)
    (hj : EqE (rs j) (foldCandidates .compose (fun k => .name (ns.nonce i k)))) :
    ¬ EqE ((frame ns swap left right).eval recipe) (foldCandidates .compose rs) := by
  intro he
  have hrepl := foldCandidates_replace rs j _ hj
  have hmem : (Term.name (V := Empty) (ns.nonce i 0)).baseClass ∈
      (foldCandidates .compose (fun k =>
        if k = j then foldCandidates .compose (fun k => Term.name (ns.nonce i k)) else rs k)).composeFactors := by
    apply (mem_foldCandidates_compose _ _).mpr
    refine ⟨j, ?_⟩
    simp only [↓reduceIte]
    apply (mem_foldCandidates_compose _ _).mpr
    exact ⟨0, by simp [Term.composeFactors]⟩
  exact frame_nonce_factor_not_deducible ns swap left right recipe hp
    (ns.nonce_mem_nonceNames i 0) _ hmem (he.trans hrepl)

/-- An accepted public ballot cannot borrow an honest aggregate proof for a
component. The single-candidate boundary uses weeding instead of a strict count. -/
theorem accepted_component_not_honest_aggregate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board)
    (j : Fin (n + 1)) (i : Fin 2) :
    ¬ EqE (((frame ns swap left right).eval recipe).project (n + 1 + j.val))
      (aggregateProof ns i ((choice swap left right i).value)) := by
  intro hborrow
  by_cases hn : n = 0
  · subst n
    fin_cases j
    have hagg : EqE (aggregateProof ns i ((choice swap left right i).value))
        ((ballot ns i ((choice swap left right i).value)).project 1) :=
      (ballot_project_proof ns i ((choice swap left right i).value) 0).symm
    exact accepted_component_proof_not_reused ha (hboard i)
      (honest_proofs_valid ns i (choice swap left right i).value (choice swap left right i).valid) 0 0 (hborrow.trans hagg).symm
  · have hn' : 0 < n := by omega
    obtain ⟨v⟩ := (proofValid_iff_values _ _).mp ha.1
    have hnonce := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp
      ((v.componentProof j).symm.trans hborrow)).2.1
    obtain ⟨z, hz, hez⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value)
      (recipe.project (2 * (n + 1))) (hp.project _)
    have hez' : EqE ((frame ns swap left right).eval z)
        (((frame ns swap left right).eval recipe).project (2 * (n + 1))) := by
      simpa only [Frame.eval, Term.subst_project] using hez.symm
    have hvalue := hez'.trans v.aggregateProof
    rcases minimum_proof_form ns swap left right ns.nonceNames z hz hvalue with
      ⟨a, r, m, c, hr⟩ | ⟨k, l, hr⟩ | ⟨k, hr⟩
    · subst z
      have hr := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hvalue).2.1
      exact frame_nonce_fold_not_deducible ns swap left right r hz.isPublic.2.1 v.nonce j i hnonce hr
    · subst z
      have hv : EqE ((frame ns swap left right).eval ((Term.var k.succ).project (n + 1 + l.val)))
          (componentProof ns k ((choice swap left right k).value) l) := by
        simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
          ballot_project_proof ns k ((choice swap left right k).value) l
      have hr := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp (hv.symm.trans hvalue)).2.1.symm
      exact nonce_fold_not_eq_small_normal hn' v.nonce j (ns.nonce i) hnonce
        (.name (ns.nonce k l)) (name_irreducible _) (by simp [Term.composeFactors]) hr
    · subst z
      have hv : EqE ((frame ns swap left right).eval ((Term.var k.succ).project (2 * (n + 1))))
          (aggregateProof ns k ((choice swap left right k).value)) := by
        simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
          ballot_project_aggregate ns k ((choice swap left right k).value)
      have hr := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp (hv.symm.trans hvalue)).2.1.symm
      exact nonce_fold_not_eq_small_normal hn' v.nonce j (ns.nonce i) hnonce
        _ (named_nonce_fold_irreducible (ns.nonce k)) (by rw [named_nonce_fold_card]) hr

/-- Every minimum accepted component proof is explicitly constructed once the
actual public ballot and board premises exclude both kinds of borrowed proof. -/
theorem minimum_accepted_component_proof_constructed (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board)
    (j : Fin (n + 1)) (proof : Recipe 3)
    (hm : MinimalRecipe ns.nonceNames (frame ns swap left right).value proof)
    (he : EqE ((frame ns swap left right).eval proof)
      (((frame ns swap left right).eval recipe).project (n + 1 + j.val))) :
    ∃ a r m c, proof = .spk a r m c := by
  rcases minimum_accepted_component_proof_form ns swap left right ns.nonceNames board _
    ha hboard j proof hm he with hc | ⟨i, hi⟩
  · exact hc
  · subst proof
    have hv : EqE ((frame ns swap left right).eval ((Term.var i.succ).project (2 * (n + 1))))
        (aggregateProof ns i ((choice swap left right i).value)) := by
      simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
        ballot_project_aggregate ns i ((choice swap left right i).value)
    exact False.elim (accepted_component_not_honest_aggregate ns swap left right recipe hp board
      ha hboard j i (he.symm.trans hv))

/-- Semantic nonces of all accepted ciphertext components have public recipes.
The proof chooses a minimum proof-field recipe, not a minimum whole ballot. -/
theorem accepted_component_public_nonce (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board)
    (v : BallotValues n (publicKey ns) ((frame ns swap left right).eval recipe)) (j : Fin (n + 1)) :
    ∃ r : Recipe 3, r.Public ns.nonceNames ∧ EqE ((frame ns swap left right).eval r) (v.nonce j) := by
  obtain ⟨z, hz, hez⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value)
    (recipe.project (n + 1 + j.val)) (hp.project _)
  have hez' : EqE ((frame ns swap left right).eval z)
      (((frame ns swap left right).eval recipe).project (n + 1 + j.val)) := by
    simpa only [Frame.eval, Term.subst_project] using hez.symm
  obtain ⟨a, r, m, c, hr⟩ := minimum_accepted_component_proof_constructed ns swap left right
    recipe hp board ha hboard j z hz hez'
  subst z
  exact ⟨r, hz.isPublic.2.1, ((EqE.spk_iff _ _ _ _ _ _ _ _).mp
    (hez'.trans (v.componentProof j))).2.1⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
