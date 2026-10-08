import ExplainableCrypto.Helios.Symbolic.PaddedPayloadMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat} {restricted : Finset Nat}

/-- With one public constructor, grouped nonce and payload are its actual
components. Minimum raw multiplication leaves therefore make both minimum. -/
theorem CiphertextAssembly.single_constructed_components_minimum (φ : Frame restricted 3)
    (t : CiphertextAssembly n)
    (hl : ∀ a ∈ t.recipe.mulLeaves, MinimalRecipe restricted φ.value a)
    (hc : t.constructedCount=1) :
    match t.group with
    | .constructed r p | .mixed r p _ => MinimalRecipe restricted φ.value r ∧ MinimalRecipe restricted φ.value p
    | .honest _ => True := by
  induction t with
  | constructed k r p =>
    have hm := hl (.ternary .penc k r p) (by simp only [recipe,Term.mulLeaves,Multiset.mem_singleton])
    exact ⟨hm.subterm (.ternarySecond .penc k .hole p),hm.subterm (.ternaryThird .penc k r .hole)⟩
  | honest i => trivial
  | mul a b ia ib =>
    have hla : ∀ x ∈ a.recipe.mulLeaves, MinimalRecipe restricted φ.value x :=
      fun x hx => hl x (Multiset.mem_add.mpr (Or.inl hx))
    have hlb : ∀ x ∈ b.recipe.mulLeaves, MinimalRecipe restricted φ.value x :=
      fun x hx => hl x (Multiset.mem_add.mpr (Or.inr hx))
    have ca := a.group_occurrence_budget
    have cb := b.group_occurrence_budget
    cases ha : a.group <;> cases hb : b.group <;>
      simp only [group,ha,hb,CiphertextGroup.merge,constructedCount] at ca cb hc ia ib ⊢
    all_goals first | omega | exact ia hla (by omega) | exact ib hlb (by omega)

/-- Full mixed minimum size follows from a minimum nonce and a padded-minimum
payload. Every minimum competitor retains the same honest indexed cost. -/
theorem minimum_mixed_of_minimum_components (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r p : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (hp : PaddedMinimalRecipe ns.restricted (frame ns swap left right).value p)
    (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (mixedCombinationRecipe r p a) := by
  have hpublic := mixedCombination_public r p hr.isPublic hp.1 a
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hpublic
  have hsub : ns.nonceNames ⊆ ns.restricted := fun _ h => Finset.mem_union_right _ h
  obtain ⟨t,s,q,b,ht,hg,_,hi,hn,hpad,hcst⟩ := minimum_mixed_combination_origin ns hf swap left right
    r p (hr.isPublic.of_subset hsub) (hp.1.of_subset hsub) a m hm he.symm
  have hs := t.group_public (ht.symm ▸ hm.isPublic)
  rw [hg] at hs
  have hnonce := hr.least s hs.1 hn.symm
  have hpayload := hp.2 q hs.2 hpad.symm
  have hhonest := combinationRecipe_nodeCount_eq hi
  apply hm.of_equivalent_size hpublic he
  simp only [mixedCombinationRecipe,Term.nodeCount] at hcst ⊢
  omega

/-- The sole public constructor's minimum components yield a minimum mixed
representative after zero-padded payload minimization. Only key-coherence
transfer uses smaller observations; payload replacement is raw padded E0 equality. -/
theorem single_mixed_shared_of_smaller_observations (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    (hpublic : t.recipe.Public ns.restricted)
    (hl : ∀ x ∈ t.recipe.mulLeaves, MinimalRecipe ns.restricted (frame ns swap left right).value x)
    (hcount : t.constructedCount=1) {r p : Recipe 3} {a : Combination (HonestIndex n)}
    (hg : t.group=.mixed r p a) (hc : t.Coherent (frame ns swap left right))
    (hobs : Frame.ObservationsBelow (frame ns swap left right) (frame ns swap' left right) t.recipe.nodeCount) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) t.recipe := by
  have hcomponents := t.single_constructed_components_minimum (frame ns swap left right) hl hcount
  rw [hg] at hcomponents
  obtain ⟨q,hq,hpad,_⟩ := padded_minimum_representative ns swap left right ns.restricted p
    hcomponents.2.isPublic (fun x hx => hcomponents.2.add_atom hx)
  have hm := minimum_mixed_of_minimum_components ns hf swap left right r q hcomponents.1 hq a
  have hn := hcomponents.1.isPublic.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
  have he (s : Bool) : EqE ((frame ns s left right).eval (mixedCombinationRecipe r p a))
      ((frame ns s left right).eval (mixedCombinationRecipe r q a)) :=
    (mixedCombination_equality_iff ns hf s left right r p r q hn hn a a).mpr
      ⟨rfl,.refl _,hpad.sound.subst _⟩
  have hc' := (t.coherent_transfer _ _ hpublic hobs).mp hc
  exact ⟨mixedCombinationRecipe r q a,hm,
    (t.mixed_compression_value ns swap left right hg hc).trans (he swap),
    (t.mixed_compression_value ns swap' left right hg hc').trans (he swap')⟩

/-- All multiplication classes share a source-minimum representative under
the two smaller-recipe hypotheses supplied by simultaneous induction. No
successful-destructor transport premise is required for this operator case. -/
theorem minimum_children_mul_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hforward : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right) (Term.binary .mul a b).nodeCount)
    (hreverse : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right) (Term.binary .mul a b).nodeCount) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (.binary .mul a b) := by
  classical
  by_cases hm : MinimalRecipe ns.restricted (frame ns swap left right).value (.binary .mul a b)
  · exact .of_minimal hm
  by_cases hv : ((frame ns swap left right).eval (.binary .mul a b)).CiphertextValue
  · obtain ⟨t,ht,hp,hc,hg⟩ := nonminimum_ciphertext_product_public_group ns hf swap left right a b ha hb hm hv
    have hft : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right) t.recipe.nodeCount := ht.symm ▸ hforward
    have hrt : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right) t.recipe.nodeCount := ht.symm ▸ hreverse
    rcases hg with ⟨nr,p,hg⟩ | ⟨nr,p,c,hg⟩
    · cases t with
      | constructed _ _ _ => cases ht
      | honest _ => simp only [CiphertextAssembly.recipe,Term.project] at ht; cases ht
      | mul u v => exact ht ▸ constructed_mul_shared_of_two_way_minima ns hf swap swap' left right u v hp hg hc hft hrt
    · by_cases hcount : 2 ≤ t.constructedCount
      · exact ht ▸ mixed_compression_shared_of_two_way_minima ns hf swap swap' left right t hp hg hc hcount hft hrt
      · have hpos := t.mixed_constructedCount_pos hg
        have hleaf : ∀ x ∈ t.recipe.mulLeaves, MinimalRecipe ns.restricted (frame ns swap left right).value x := by
          intro x hx
          rw [ht] at hx
          exact (Multiset.mem_add.mp hx).elim (ha.mul_leaf) (hb.mul_leaf)
        exact ht ▸ single_mixed_shared_of_smaller_observations ns hf swap swap' left right t hp hleaf
          (by omega) hg hc (observationsBelow_of_two_way_minima ns hf swap swap' left right _ hft hrt)
  · exact minimum_children_non_ciphertext_mul_shared ns swap left right _ a b ha hb hv hforward

end ExplainableCrypto.Helios.Symbolic.Historical.General
