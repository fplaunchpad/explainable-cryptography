import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedMinimumLifting

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Existing syntax key transfer works for an entire assembly even when its
parent is nonminimum. This supplies destination ciphertext values for later
compression without introducing a separate coherence premise. -/
theorem expanded_assembly_ciphertext_value_transfer (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (t : CiphertextAssembly n (ExpandedHandles n)) (hp : (t.recipeWith expandedOld).Public ns.restricted)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (t.recipeWith expandedOld).nodeCount)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    ((expandedFrame ns swap' left right rs).eval (t.recipeWith expandedOld)).CiphertextValue := by
  obtain ⟨k,r,p,he⟩ := hv
  obtain ⟨key,_,_,_,nonce,message,hv⟩ := expanded_ciphertext_syntax_key_transfer ns swap swap' left right rs hn
    (t.recipeWith expandedOld) (t.recipeWith_ciphertext_syntax expandedOld) hp hobs he
  exact ⟨_,nonce,message,hv⟩

/-- Grouped interpretation gives the actual compressed public constructor.
Its value premise derives all common-key agreements, including reducible keys. -/
theorem expanded_constructed_compression_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (t : CiphertextAssembly n (ExpandedHandles n)) {r p : Recipe (ExpandedHandles n)}
    (hg : t.group = .constructed r p)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    EqE ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld))
      ((expandedFrame ns swap left right rs).eval (.ternary .penc (t.keyRecipeWith expandedOld) r p)) := by
  simpa only [hg,CiphertextGroup.nonce,CiphertextGroup.message,Frame.eval,Term.subst] using
    expanded_assembly_grouped_value ns swap left right rs t hv

/-- A minimum constructed-only ciphertext assembly cannot have a nontrivial
multiplication root: its public compression would be strictly smaller. -/
theorem expanded_minimum_constructed_group_recipe (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (t : CiphertextAssembly n (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (t.recipeWith expandedOld))
    {r p : Recipe (ExpandedHandles n)} (hg : t.group = .constructed r p)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    t.recipeWith expandedOld = .ternary .penc (t.keyRecipeWith expandedOld) r p := by
  cases t with
  | constructed k nr m => cases hg; rfl
  | honest i => cases hg
  | mul a b => exact False.elim (hm.no_smaller
      ((a.mul b).constructed_compression_publicWith expandedOld hm.isPublic hg)
      (expanded_constructed_compression_value ns swap left right rs (a.mul b) hg hv)
      (a.constructed_mul_compression_smallerWith b expandedOld hg))

/-- A source-minimum ciphertext with a publicly denotable nonce has raw
constructor syntax. Opaque protection and strict compression discharge both
honest/mixed and nontrivial constructed-product alternatives. -/
theorem expanded_minimum_ciphertext_public_nonce_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r nonce : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hnonce : nonce.Public ns.restricted) {key message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r)
      (.ternary .penc key ((expandedFrame ns swap left right rs).eval nonce) message)) :
    ∃ k u p, r = .ternary .penc k u p := by
  obtain ⟨t,rfl,_,_,_,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn r hm ⟨_,_,_,he⟩
  have hv := expanded_assembly_grouped_value ns swap left right rs t ⟨_,_,_,he⟩
  have heNonce := ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans he)).2.1
  obtain ⟨u,p,hg⟩ := t.group.constructed_of_public_nonce_of_opaque ns _
    (expanded_frame_opaque_protected ns swap left right rs hp)
    (fun i => Finset.mem_union_right _ (ns.nonce_mem_nonceNames i.1 i.2)) nonce hnonce heNonce
  exact ⟨t.keyRecipeWith expandedOld,u,p,
    expanded_minimum_constructed_group_recipe ns swap left right rs t hm hg ⟨_,_,_,he⟩⟩

/-- Strict constructed compression preserves both actual frames. A smaller
shared representative of the compression yields one for the original product. -/
theorem expanded_constructed_mul_shared_of_smaller_observations (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b : CiphertextAssembly n (ExpandedHandles n))
    (hp : ((a.mul b).recipeWith expandedOld).Public ns.restricted) {r p : Recipe (ExpandedHandles n)}
    (hg : (a.mul b).group = .constructed r p)
    (hv : ((expandedFrame ns swap left right rs).eval ((a.mul b).recipeWith expandedOld)).CiphertextValue)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      ((a.mul b).recipeWith expandedOld).nodeCount)
    (hsmall : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      ((a.mul b).recipeWith expandedOld).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      ((a.mul b).recipeWith expandedOld) := by
  have hv' := expanded_assembly_ciphertext_value_transfer ns swap swap' left right rs hn (a.mul b) hp hobs hv
  exact (hsmall _ ((a.mul b).constructed_compression_publicWith expandedOld hp hg)
    (a.constructed_mul_compression_smallerWith b expandedOld hg)).of_shared_equivalent
      (expanded_constructed_compression_value ns swap left right rs (a.mul b) hg hv)
      (expanded_constructed_compression_value ns swap' left right rs (a.mul b) hg hv')

/-- The exact two-way smaller-minimum hypotheses for simultaneous induction
supply all observations. The constructed-only ciphertext product branch has
no residual key-coherence or observation premise. -/
theorem accepted_expanded_constructed_mul_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : CiphertextAssembly n (ExpandedHandles n))
    (hpublic : ((a.mul b).recipeWith expandedOld).Public ns.restricted) {r p : Recipe (ExpandedHandles n)}
    (hg : (a.mul b).group = .constructed r p)
    (hv : ((expandedFrame ns swap left right rs).eval ((a.mul b).recipeWith expandedOld)).CiphertextValue)
    (hforward : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      ((a.mul b).recipeWith expandedOld).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs)
      ((a.mul b).recipeWith expandedOld).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      ((a.mul b).recipeWith expandedOld) :=
  expanded_constructed_mul_shared_of_smaller_observations ns swap swap' left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) a b hpublic hg hv
    (accepted_expanded_observationsBelow_of_two_way_minima ns hf swap swap' left right rs hp haccept _ hforward hreverse) hforward

end ExplainableCrypto.Helios.Symbolic.Historical.General
