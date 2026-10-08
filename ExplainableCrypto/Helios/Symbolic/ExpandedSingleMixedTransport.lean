import ExplainableCrypto.Helios.Symbolic.ExpandedPaddedMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedMixedMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat} {restricted : Finset Nat}

/-- With one constructed occurrence, grouped nonce/payload are actual
components of that leaf. Minimum raw multiplication leaves make both minimum. -/
theorem CiphertextAssembly.single_constructed_components_minimumWith (φ : Frame restricted handles)
    (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    (hl : ∀ a ∈ (t.recipeWith old).mulLeaves, MinimalRecipe restricted φ.value a)
    (hc : t.constructedCount=1) :
    match t.group with
    | .constructed r p | .mixed r p _ => MinimalRecipe restricted φ.value r ∧ MinimalRecipe restricted φ.value p
    | .honest _ => True := by
  induction t with
  | constructed k r p =>
    have hm := hl (.ternary .penc k r p) (by simp only [recipeWith,Term.mulLeaves,Multiset.mem_singleton])
    exact ⟨hm.subterm (.ternarySecond .penc k .hole p),hm.subterm (.ternaryThird .penc k r .hole)⟩
  | honest i => trivial
  | mul a b ia ib =>
    have hla : ∀ x ∈ (a.recipeWith old).mulLeaves, MinimalRecipe restricted φ.value x :=
      fun x hx => hl x (Multiset.mem_add.mpr (Or.inl hx))
    have hlb : ∀ x ∈ (b.recipeWith old).mulLeaves, MinimalRecipe restricted φ.value x :=
      fun x hx => hl x (Multiset.mem_add.mpr (Or.inr hx))
    have ca := a.group_occurrence_budgetWith old
    have cb := b.group_occurrence_budgetWith old
    cases ha : a.group <;> cases hb : b.group <;>
      simp only [group,ha,hb,CiphertextGroup.merge,constructedCount] at ca cb hc ia ib ⊢
    all_goals first | omega | exact ia hla (by omega) | exact ib hlb (by omega)

/-- A minimum nonce and globally padded-minimum payload give a global mixed
minimum. Every competitor pays the same indexed honest occurrence cost. -/
theorem expanded_minimum_mixed_of_minimum_components (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hpub : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r p : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hp : PaddedMinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value p)
    (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (mixedCombinationRecipeWith expandedOld r p a) := by
  have hpublic := mixedCombinationRecipeWith_public expandedOld r p hr.isPublic hp.1 a
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpublic
  obtain ⟨t,s,q,b,ht,hg,_,hi,hneq,hpad,hcst⟩ := expanded_minimum_mixed_combination_origin ns hf swap left right rs hpub hn
    r p hr.isPublic hp.1 a m hm he.symm
  have hs := t.group_publicWith expandedOld (ht.symm ▸ hm.isPublic)
  rw [hg] at hs
  have hnonce := hr.least s hs.1 hneq.symm
  have hpayload := hp.2 q hs.2 hpad.symm
  have hhonest := combinationRecipe_nodeCount_eq hi
  apply hm.of_equivalent_size hpublic he
  simp only [mixedCombinationRecipeWith,Term.nodeCount,combinationRecipeWith_nodeCount] at hcst ⊢
  omega

/-- The one-constructor mixed case uses shared numeric-handle tables to
minimize padded payloads globally. Smaller observations are needed only to
transfer assembly ciphertext-valuedness and hence election-key agreement. -/
theorem accepted_expanded_single_mixed_shared_of_smaller_observations (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (t : CiphertextAssembly n (ExpandedHandles n)) (hpublic : (t.recipeWith expandedOld).Public ns.restricted)
    (hl : ∀ x ∈ (t.recipeWith expandedOld).mulLeaves, MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value x)
    (hcount : t.constructedCount=1) {r p : Recipe (ExpandedHandles n)} {a : Combination (HonestIndex n)}
    (hg : t.group=.mixed r p a)
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue)
    (hobs : Frame.ObservationsBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (t.recipeWith expandedOld).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (t.recipeWith expandedOld) := by
  choose numbers _ hnum using fun j => accepted_sequence_tally_numeric ns hf left right rs hp haccept j
  let ν := expandedNumericHandles numbers
  have hn := accepted_expanded_results_numeric ns hf left right rs hp haccept swap
  have hcomponents := t.single_constructed_components_minimumWith (expandedFrame ns swap left right rs) expandedOld hl hcount
  rw [hg] at hcomponents
  obtain ⟨q,hq,ha,ht,_⟩ := expanded_padded_minimum_representative ns swap left right rs numbers
    (fun j => hnum j swap) ns.restricted p hcomponents.2.isPublic (fun x hx => hcomponents.2.add_numeric_atom ν hx)
  have hm := expanded_minimum_mixed_of_minimum_components ns hf swap left right rs hp hn r q hcomponents.1 hq a
  have he (s : Bool) : EqE ((expandedFrame ns s left right rs).eval (mixedCombinationRecipeWith expandedOld r p a))
      ((expandedFrame ns s left right rs).eval (mixedCombinationRecipeWith expandedOld r q a)) := by
    have hpad := padded_eqE_of_addNumericSummary (expandedFrame ns s left right rs).value ν
      (expanded_numeric_handle_value ns s left right rs numbers (fun j => hnum j s)) ha.symm ht.symm
    have heq := (expanded_group_ciphertext_eq_iff ns hf s left right rs hp (.mixed r p a) (.mixed r q a)
      ⟨hcomponents.1.isPublic,hcomponents.2.isPublic⟩ ⟨hcomponents.1.isPublic,hq.1⟩ (publicKey ns) (publicKey ns)).mpr
      ⟨.refl _,rfl,.refl _,hpad⟩
    exact (expanded_mixedCombination_value ns s left right rs r p a).trans
      (heq.trans (expanded_mixedCombination_value ns s left right rs r q a).symm)
  have hv' := expanded_assembly_ciphertext_value_transfer ns swap swap' left right rs hn t hpublic hobs hv
  exact ⟨mixedCombinationRecipeWith expandedOld r q a,hm,
    (expanded_mixed_compression_value ns swap left right rs t hg hv).trans (he swap),
    (expanded_mixed_compression_value ns swap' left right rs t hg hv').trans (he swap')⟩

/-- Every multiplication class has a shared source-minimum representative
under the two strict smaller-minimum hypotheses of simultaneous induction.
No observation, coherence or successful-destructor premise remains at this interface. -/
theorem accepted_expanded_minimum_children_mul_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hforward : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (Term.binary .mul a b).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs) (Term.binary .mul a b).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.binary .mul a b) := by
  classical
  by_cases hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .mul a b)
  · exact .of_minimal hm
  by_cases hv : ((expandedFrame ns swap left right rs).eval (.binary .mul a b)).CiphertextValue
  · have hn := accepted_expanded_results_numeric ns hf left right rs hp haccept swap
    obtain ⟨u,v,hu,hvRecipe,hpublic,hg⟩ := expanded_nonminimum_ciphertext_product_public_group ns hf swap left right rs hp hn a b ha hb hm hv
    let t := u.mul v
    have ht : t.recipeWith expandedOld = .binary .mul a b := by simp only [t,CiphertextAssembly.recipeWith,hu,hvRecipe]
    have hft : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (t.recipeWith expandedOld).nodeCount := ht.symm ▸ hforward
    have hrt : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs) (t.recipeWith expandedOld).nodeCount := ht.symm ▸ hreverse
    have hvt : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue := ht.symm ▸ hv
    rcases hg with ⟨nr,p,hg⟩ | ⟨nr,p,c,hg⟩
    · exact ht ▸ accepted_expanded_constructed_mul_shared_of_two_way_minima ns hf swap swap' left right rs hp haccept
        u v hpublic hg hvt hft hrt
    · by_cases hcount : 2 ≤ t.constructedCount
      · exact ht ▸ accepted_expanded_mixed_compression_shared_of_two_way_minima ns hf swap swap' left right rs hp haccept
          t hpublic hg hvt hcount hft hrt
      · have hpos := t.mixed_constructedCount_posWith expandedOld hg
        have hleaf : ∀ x ∈ (t.recipeWith expandedOld).mulLeaves, MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value x := by
          intro x hx
          rw [ht] at hx
          exact (Multiset.mem_add.mp hx).elim ha.mul_leaf hb.mul_leaf
        exact ht ▸ accepted_expanded_single_mixed_shared_of_smaller_observations ns hf swap swap' left right rs hp haccept
          t hpublic hleaf (by omega) hg hvt
          (accepted_expanded_observationsBelow_of_two_way_minima ns hf swap swap' left right rs hp haccept _ hft hrt)
  · exact accepted_expanded_minimum_children_non_ciphertext_mul_shared ns hf swap swap' left right rs hp haccept a b ha hb hv hforward

end ExplainableCrypto.Helios.Symbolic.Historical.General
