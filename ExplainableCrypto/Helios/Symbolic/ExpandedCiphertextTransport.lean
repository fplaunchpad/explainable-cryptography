import ExplainableCrypto.Helios.Symbolic.ExpandedCiphertextAssembly

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The full ciphertext equality branch for accepted expanded frames. Exact
assemblies, key agreement in both worlds, and original recipe-size bounds are
all derived. Only source minima and strictly smaller observations are assumed. -/
theorem accepted_expanded_minimum_ciphertext_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    (hvr : ((expandedFrame ns swap left right rs).eval r).CiphertextValue)
    (hvs : ((expandedFrame ns swap left right rs).eval s).CiphertextValue)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s) ↔
      EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  have hvr' := accepted_expanded_minimum_ciphertext_value_transfer ns hf swap swap' left right rs hp ha
    r hr (hobs.mono (by omega)) hvr
  have hvs' := accepted_expanded_minimum_ciphertext_value_transfer ns hf swap swap' left right rs hp ha
    s hs (hobs.mono (by omega)) hvs
  obtain ⟨a,rfl,hga,hba,hka,hsa⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn r hr hvr
  obtain ⟨b,rfl,hgb,hbb,hkb,hsb⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn s hs hvs
  have hk := hobs (a.keyRecipeWith expandedOld) (b.keyRecipeWith expandedOld) hka hkb (by omega)
  have hg := CiphertextGroup.observation_transfer _ _ a.group b.group hga hgb hba hbb hobs
  exact (expanded_assembly_equality_iff ns hf swap left right rs hp a b hr.isPublic hs.isPublic hvr hvs).trans
    ((and_congr hk hg).trans
      (expanded_assembly_equality_iff ns hf swap' left right rs hp a b hr.isPublic hs.isPublic hvr' hvs').symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
