import ExplainableCrypto.Helios.Symbolic.CombinationHandleTools
import ExplainableCrypto.Helios.Symbolic.ExpandedCiphertextAssembly

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The retained old-handle combination has exactly its original homomorphic
value, independently of published submissions or their acceptance. -/
theorem expanded_combination_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (a : Combination (HonestIndex n)) :
    EqE ((expandedFrame ns swap left right rs).eval (combinationRecipeWith expandedOld a))
      (.ternary .penc (publicKey ns) (combinationNonce ns a) (combinationMessage swap left right a)) := by
  rw [combinationRecipeWith,expanded_old_recipe_value]
  exact combination_value ns swap left right a

/-- Every globally minimum equivalent of an honest combination in the actual
expanded frame has honest-only syntax and the same indexed occurrence bag. -/
theorem expanded_minimum_honest_combination_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (a : Combination (HonestIndex n))
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      ((expandedFrame ns swap left right rs).eval (combinationRecipeWith expandedOld a))) :
    ∃ b, r = combinationRecipeWith expandedOld b ∧ b.indices = a.indices := by
  have hv := he.trans (expanded_combination_value ns swap left right rs a)
  obtain ⟨t,rfl,hpub,_,_,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn r hm ⟨_,_,_,hv⟩
  have hgvalue := expanded_assembly_grouped_value ns swap left right rs t ⟨_,_,_,hv⟩
  have hparts := (EqE.penc_iff _ _ _ _ _ _).mp (hgvalue.symm.trans hv)
  have obs := (expanded_group_components_eq_iff ns hf swap left right rs hp t.group (.honest a)
    hpub trivial).mp hparts.2
  cases hg : t.group with
  | constructed r p => simp only [hg,CiphertextGroup.Observation] at obs
  | mixed r p b => simp only [hg,CiphertextGroup.Observation] at obs
  | honest b => exact ⟨b,t.recipeWith_of_honest_group expandedOld hg,
      by simpa only [hg,CiphertextGroup.Observation] using obs⟩

/-- Honest combinations are globally minimum even against recipes using all
published partial/result handles. Numeric origins and freshness are explicit. -/
theorem expanded_minimum_honest_combination (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (combinationRecipeWith expandedOld a) := by
  have hpub := combinationRecipeWith_public (handles := ExpandedHandles n) expandedOld ns.restricted a
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpub
  obtain ⟨b,rfl,hb⟩ := expanded_minimum_honest_combination_origin ns hf swap left right rs hp hn m hm a he.symm
  exact hm.of_equivalent_size hpub he (by
    rw [combinationRecipeWith_nodeCount,combinationRecipeWith_nodeCount,combinationRecipe_nodeCount_eq hb])

/-- Accepted public submissions supply the numeric result premise. -/
theorem accepted_expanded_minimum_honest_combination (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (combinationRecipeWith expandedOld a) :=
  expanded_minimum_honest_combination ns hf swap left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) a

/-- The honest combination itself is a shared minimum with any destination.
No smaller-observation or smaller-minimum premise is needed. -/
theorem expanded_honest_combination_shared (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a : Combination (HonestIndex n)) (ψ : Frame ns.restricted (ExpandedHandles n)) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) ψ (combinationRecipeWith expandedOld a) :=
  .of_minimal (expanded_minimum_honest_combination ns hf swap left right rs hp hn a)

/-- Exact honest assembly syntax inherits the global combination minimum. -/
theorem expanded_minimum_assembly_of_honest_group (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (t : CiphertextAssembly n (ExpandedHandles n)) {a : Combination (HonestIndex n)} (hg : t.group = .honest a) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (t.recipeWith expandedOld) := by
  rw [t.recipeWith_of_honest_group expandedOld hg]
  exact expanded_minimum_honest_combination ns hf swap left right rs hp hn a

/-- A nonminimum ciphertext product with minimum children must contain a
constructed contribution. Its exact assembly and actual ciphertext value are
retained; honest-only groups are excluded by a global minimum theorem. -/
theorem expanded_nonminimum_ciphertext_product_public_group (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hm : ¬ MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .mul a b))
    (hv : ((expandedFrame ns swap left right rs).eval (.binary .mul a b)).CiphertextValue) :
    ∃ u v : CiphertextAssembly n (ExpandedHandles n), u.recipeWith expandedOld = a ∧ v.recipeWith expandedOld = b ∧
      ((u.mul v).recipeWith expandedOld).Public ns.restricted ∧
      (((∃ r p, (u.mul v).group = .constructed r p) ∨ (∃ r p c, (u.mul v).group = .mixed r p c))) := by
  obtain ⟨k,nr,m,he⟩ := hv
  obtain ⟨_,_,_,_,hea,heb,_,_⟩ := he.mul_penc_inversion
  obtain ⟨u,hu,_,_,_,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn a ha ⟨_,_,_,hea⟩
  obtain ⟨v,hv,_,_,_,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn b hb ⟨_,_,_,heb⟩
  have ht : (u.mul v).recipeWith expandedOld = .binary .mul a b := by
    simp only [CiphertextAssembly.recipeWith,hu,hv]
  refine ⟨u,v,hu,hv,ht ▸ ⟨ha.isPublic,hb.isPublic⟩,?_⟩
  cases hg : (u.mul v).group with
  | constructed r p => exact Or.inl ⟨r,p,rfl⟩
  | mixed r p c => exact Or.inr ⟨r,p,c,rfl⟩
  | honest c =>
    have hmin := expanded_minimum_assembly_of_honest_group ns hf swap left right rs hp hn (u.mul v) hg
    exact False.elim (hm (ht ▸ hmin))

end ExplainableCrypto.Helios.Symbolic.Historical.General
