import ExplainableCrypto.Helios.Symbolic.MixedHandleTools
import ExplainableCrypto.Helios.Symbolic.ExpandedHonestMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedCompression

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- E3 evaluates the public constructor and the existing honest combination;
the expanded election-key handle supplies their common key. -/
theorem expanded_mixedCombination_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (r p : Recipe (ExpandedHandles n)) (a : Combination (HonestIndex n)) :
    EqE ((expandedFrame ns swap left right rs).eval (mixedCombinationRecipeWith expandedOld r p a))
      (.ternary .penc (publicKey ns)
        (.binary .compose ((expandedFrame ns swap left right rs).eval r) (combinationNonce ns a))
        (.binary .add ((expandedFrame ns swap left right rs).eval p) (combinationMessage swap left right a))) := by
  have hk : EqE ((expandedFrame ns swap left right rs).eval (.var (expandedOld 0))) (publicKey ns) := by
    rw [expanded_election_handle_value]; exact .refl _
  exact (EqE.binary .mul (.ternary .penc hk (.refl _) (.refl _))
    (expanded_combination_value ns swap left right rs a)).trans (RootStep.homomorphic _ _ _ _ _).sound

/-- An actual ciphertext value forces every key to agree. Any honest
contribution pins that key to the election key, permitting mixed compression. -/
theorem expanded_mixed_compression_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (t : CiphertextAssembly n (ExpandedHandles n)) {r p : Recipe (ExpandedHandles n)}
    {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    EqE ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld))
      ((expandedFrame ns swap left right rs).eval (mixedCombinationRecipeWith expandedOld r p a)) := by
  obtain ⟨key,nonce,message,he⟩ := hv
  have hh := expanded_honest_selector_value ns swap left right rs
  have hk := t.key_agreement_of_valueWith ns _ expandedOld swap left right hh he
  have hkey := t.key_agreement_public_key_of_nonconstructed ns _ hk (by
    intro u v hu; rw [hg] at hu; cases hu)
  have hvalue := t.grouped_valueWith ns _ expandedOld swap left right hh key hk
  have helection := hvalue.trans (.ternary .penc hkey.symm (.refl _) (.refl _))
  exact helection.trans (by simpa only [hg,CiphertextGroup.nonce,CiphertextGroup.message] using
    (expanded_mixedCombination_value ns swap left right rs r p a).symm)

/-- Two constructors in a minimum mixed assembly contradict strict public
compression. Minimum mixed assemblies have exactly one constructed occurrence. -/
theorem expanded_minimum_mixed_constructedCount_eq_one (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (t : CiphertextAssembly n (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (t.recipeWith expandedOld))
    {r p : Recipe (ExpandedHandles n)} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    t.constructedCount = 1 := by
  have hp := t.mixed_constructedCount_posWith expandedOld hg
  by_contra hn
  exact hm.no_smaller (t.mixed_compression_publicWith expandedOld hm.isPublic hg)
    (expanded_mixed_compression_value ns swap left right rs t hg hv)
    (t.mixed_compression_smallerWith expandedOld hg (by omega))

/-- A minimum mixed assembly has a grouped public-key representative with
exactly the same global minimum size, independent of constructor placement. -/
theorem expanded_minimum_mixed_grouped_representative (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (t : CiphertextAssembly n (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (t.recipeWith expandedOld))
    {r p : Recipe (ExpandedHandles n)} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (mixedCombinationRecipeWith expandedOld r p a) ∧
      (mixedCombinationRecipeWith expandedOld r p a).nodeCount = (t.recipeWith expandedOld).nodeCount := by
  have hp := t.mixed_compression_publicWith expandedOld hm.isPublic hg
  have he := expanded_mixed_compression_value ns swap left right rs t hg hv
  have hcount := expanded_minimum_mixed_constructedCount_eq_one ns swap left right rs t hm hg hv
  have hcst := t.mixed_compression_costWith expandedOld hg
  have hle := hm.least _ hp he
  exact ⟨hm.of_equivalent_size hp he.symm (by omega),by omega⟩

/-- The two strict smaller-minimum induction hypotheses close mixed assemblies
with at least two constructors. Bounded observations and existing key transfer
supply destination ciphertext values, including for nonminimum source parents. -/
theorem accepted_expanded_mixed_compression_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (t : CiphertextAssembly n (ExpandedHandles n)) (hpublic : (t.recipeWith expandedOld).Public ns.restricted)
    {r p : Recipe (ExpandedHandles n)} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue)
    (hcount : 2 ≤ t.constructedCount)
    (hforward : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (t.recipeWith expandedOld).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs)
      (t.recipeWith expandedOld).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (t.recipeWith expandedOld) := by
  have hobs := accepted_expanded_observationsBelow_of_two_way_minima ns hf swap swap' left right rs hp haccept _ hforward hreverse
  have hv' := expanded_assembly_ciphertext_value_transfer ns swap swap' left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) t hpublic hobs hv
  exact (hforward _ (t.mixed_compression_publicWith expandedOld hpublic hg)
    (t.mixed_compression_smallerWith expandedOld hg hcount)).of_shared_equivalent
      (expanded_mixed_compression_value ns swap left right rs t hg hv)
      (expanded_mixed_compression_value ns swap' left right rs t hg hv')

end ExplainableCrypto.Helios.Symbolic.Historical.General
