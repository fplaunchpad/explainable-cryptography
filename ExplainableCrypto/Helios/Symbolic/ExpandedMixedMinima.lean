import ExplainableCrypto.Helios.Symbolic.ExpandedMixedCompression

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Minimum competitors of a public mixed combination retain the honest
occurrence bag, public nonce value and zero-padded public payload value. Their
single-constructor grouped representation has exactly the original minimum size. -/
theorem expanded_minimum_mixed_combination_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hpub : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r p : Recipe (ExpandedHandles n)) (hr : r.Public ns.restricted) (hp : p.Public ns.restricted)
    (a : Combination (HonestIndex n)) (m : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value m)
    (he : EqE ((expandedFrame ns swap left right rs).eval m)
      ((expandedFrame ns swap left right rs).eval (mixedCombinationRecipeWith expandedOld r p a))) :
    ∃ t : CiphertextAssembly n (ExpandedHandles n), ∃ s q b,
      t.recipeWith expandedOld=m ∧ t.group=.mixed s q b ∧ t.constructedCount=1 ∧
      b.indices=a.indices ∧ EqE ((expandedFrame ns swap left right rs).eval s) ((expandedFrame ns swap left right rs).eval r) ∧
      EqE ((expandedFrame ns swap left right rs).eval (.binary .add q (.const .zero)))
        ((expandedFrame ns swap left right rs).eval (.binary .add p (.const .zero))) ∧
      (mixedCombinationRecipeWith expandedOld s q b).nodeCount=m.nodeCount := by
  have hv := he.trans (expanded_mixedCombination_value ns swap left right rs r p a)
  obtain ⟨t,rfl,hgroup,_,_,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn m hm ⟨_,_,_,hv⟩
  have hvalue := expanded_assembly_grouped_value ns swap left right rs t ⟨_,_,_,hv⟩
  have hparts := (EqE.penc_iff _ _ _ _ _ _).mp (hvalue.symm.trans hv)
  have obs := (expanded_group_components_eq_iff ns hf swap left right rs hpub t.group (.mixed r p a)
    hgroup ⟨hr,hp⟩).mp hparts.2
  cases hg : t.group with
  | constructed s q => simp only [hg,CiphertextGroup.Observation] at obs
  | honest b => simp only [hg,CiphertextGroup.Observation] at obs
  | mixed s q b =>
    simp only [hg,CiphertextGroup.Observation] at obs
    exact ⟨t,s,q,b,rfl,hg,expanded_minimum_mixed_constructedCount_eq_one ns swap left right rs t hm hg ⟨_,_,_,hv⟩,
      obs.1,obs.2.1,obs.2.2,(expanded_minimum_mixed_grouped_representative ns swap left right rs t hm hg ⟨_,_,_,hv⟩).2⟩

/-- A minimum public nonce and a one-node public payload attain the global
mixed minimum, including when they use published handles. Every competitor
pays the same honest indexed cost and at least one payload node. -/
theorem expanded_minimum_mixed_of_minimum_nonce_atomic_payload (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hpub : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r p : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hp : p.Public ns.restricted) (hsize : p.nodeCount=1) (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (mixedCombinationRecipeWith expandedOld r p a) := by
  have hpublic := mixedCombinationRecipeWith_public expandedOld r p hr.isPublic hp a
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpublic
  obtain ⟨t,s,q,b,ht,hg,_,hi,hneq,_,hcst⟩ := expanded_minimum_mixed_combination_origin ns hf swap left right rs hpub hn
    r p hr.isPublic hp a m hm he.symm
  have hs := t.group_publicWith expandedOld (ht.symm ▸ hm.isPublic)
  rw [hg] at hs
  have hnonce := hr.least s hs.1 hneq.symm
  have hhonest := combinationRecipe_nodeCount_eq hi
  have hq := q.nodeCount_pos
  apply hm.of_equivalent_size hpublic he
  simp only [mixedCombinationRecipeWith,Term.nodeCount,combinationRecipeWith_nodeCount] at hcst ⊢
  omega

end ExplainableCrypto.Helios.Symbolic.Historical.General
