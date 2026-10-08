import ExplainableCrypto.Helios.Symbolic.HonestProofTailMinima

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat} {φ ψ : Frame restricted n}

/-- A projection from an explicit minimum pair uses its selected minimum child
as a shared representative, through a pre-substitution equation. -/
theorem SharedMinimum.projection_of_minimum_pair (a b : Recipe n)
    (hm : MinimalRecipe restricted φ.value (.binary .pair a b))
    (f : Unary) (hf : f = .fst ∨ f = .snd) :
    SharedMinimum φ ψ (.unary f (.binary .pair a b)) := by
  rcases hf with rfl | rfl
  · exact .of_recipe_eqE (hm.subterm (.binaryLeft .pair .hole b)) (RootStep.fst _ _).sound
  · exact .of_recipe_eqE (hm.subterm (.binaryRight .pair a .hole)) (RootStep.snd _ _).sound

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- All proof-valued chains on honest handles have a shared minimum. Source
minimum size of the input chain is not assumed. -/
theorem proof_chain_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) {r : Recipe 3} (v : Fin 3)
    (hc : ProjectionChain v r) {a b c d : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.spk a b c d)) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) r := by
  have voter (i : Fin 2) (hc : ProjectionChain i.succ r) :
      Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) r := by
    rcases voter_projection_proof_origin ns swap left right i hc he with ⟨j,rfl,_⟩ | ⟨rfl,_⟩
    · exact .of_minimal (minimum_component_proof_selector ns hf swap left right i j)
    · exact aggregate_selector_shared_minimum ns hf swap swap' left right i
  fin_cases v
  · exact False.elim (key_projection_chain_not_spk ns swap left right hc a b c d he)
  · exact voter 0 hc
  · exact voter 1 hc

/-- For a projection with a minimum child, only pair/ciphertext output classes
remain after explicit pairs, proof selectors, empty tails and stuck roots close.
No smaller-observation or destination-minimum premise is used. -/
theorem projection_shared_or_pair_ciphertext (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (f : Unary) (hproj : f = .fst ∨ f = .snd)
    (a : Recipe 3) (hm : MinimalRecipe ns.restricted (frame ns swap left right).value a) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.unary f a) ∨
    (((frame ns swap left right).eval (.unary f a)).PairValue ∨
      ((frame ns swap left right).eval (.unary f a)).CiphertextValue) := by
  classical
  by_cases hp : ((frame ns swap left right).eval a).PairValue
  · obtain ⟨x,y,he⟩ := hp
    rcases minimum_pair_observation_form ns swap left right ns.restricted a hm he with
      ⟨u,v,rfl⟩ | ⟨i,k,hk,rfl⟩
    · exact Or.inl (.projection_of_minimum_pair u v hm f hproj)
    · rcases hproj with rfl | rfl
      · have hfield : k < (ballotFields ns i (choice swap left right i).value).length := by
          simpa only [ballot_fields_length] using hk
        rcases ballot_field_cases ns i (choice swap left right i).value k hfield with
          ⟨j,rfl,_⟩ | ⟨j,rfl,_⟩ | ⟨rfl,_⟩
        · refine Or.inr (Or.inr ⟨publicKey ns, .name (ns.nonce i j), (choice swap left right i).value j, ?_⟩)
          change EqE ((frame ns swap left right).eval ((Term.var i.succ).project j.val)) _
          simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle, ciphertext] using
            ballot_project_ciphertext ns i (choice swap left right i).value j
        · exact Or.inl (.of_minimal (minimum_component_proof_selector ns hf swap left right i j))
        · exact Or.inl (aggregate_selector_shared_minimum ns hf swap swap' left right i)
      · by_cases hproof : n+1 ≤ k+1
        · apply Or.inl
          simpa only [Term.drop_succ_outer] using
            proof_tail_shared_minimum ns hf swap swap' left right i (k+1) hproof (by omega)
        · apply Or.inr ∘ Or.inl
          have hnext : k+1 < fieldCount n := by unfold fieldCount at *; omega
          simpa only [Term.PairValue, Term.drop_succ_outer] using
            ballot_tail_pair_value ns swap left right i (k+1) hnext

  · exact Or.inl (.of_minimal (minimum_stuck_projection_of_child ns swap left right f hproj a hm
      (fun x y he => hp ⟨x,y,he⟩)))

/-- A proof-valued successful projection is fully discharged by the preceding
classification; its result cannot also be a pair or ciphertext value. -/
theorem proof_projection_shared_minimum (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (f : Unary) (hproj : f = .fst ∨ f = .snd)
    (r : Recipe 3) (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    {a b c d : Ground}
    (he : EqE ((frame ns swap left right).eval (.unary f r)) (.spk a b c d)) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.unary f r) := by
  rcases projection_shared_or_pair_ciphertext ns hf swap swap' left right f hproj r hm with hs | hp | hc
  · exact hs
  · obtain ⟨x,y,hp⟩ := hp
    exact False.elim (spk_not_eqE_passive_binary .pair (Or.inl rfl) a b c d x y (he.symm.trans hp))
  · obtain ⟨k,nonce,p,hc⟩ := hc
    exact False.elim (penc_not_eqE_spk k nonce p a b c d (hc.symm.trans he))

end ExplainableCrypto.Helios.Symbolic.Historical.General
