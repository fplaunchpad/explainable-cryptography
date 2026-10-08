import ExplainableCrypto.Helios.Symbolic.PairMinimumTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Retain the selected key alongside the grouped component budget. This bound
uses the original tree size, including every repeated key and multiplication. -/
theorem CiphertextAssembly.key_group_budget (t : CiphertextAssembly n) :
    t.keyRecipe.nodeCount + t.group.budget ≤ t.recipe.nodeCount + 1 := by
  induction t with
  | constructed k r p =>
    simp only [keyRecipe,group,CiphertextGroup.budget,recipe,Term.nodeCount]
    omega
  | honest i =>
    simp only [keyRecipe,group,CiphertextGroup.budget,recipe,Term.project_nodeCount,Term.nodeCount]
    omega
  | mul a b ia _ =>
    have hb := b.group_budget
    have hm := CiphertextGroup.merge_budget a.group b.group
    simp only [keyRecipe,group,recipe,Term.nodeCount]
    omega

/-- A group whose nonce is public has no honest contribution. Restricted
nonce factors suffice; the names need not be fresh or pairwise distinct. -/
theorem CiphertextGroup.constructed_of_public_nonce (g : CiphertextGroup n)
    (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (r : Recipe 3) (hr : r.Public ns.nonceNames)
    (he : EqE (g.nonce ns (frame ns swap left right)) ((frame ns swap left right).eval r)) :
    ∃ u v, g = .constructed u v := by
  cases g with
  | constructed u v => exact ⟨u,v,rfl⟩
  | honest a =>
    obtain ⟨i,hi⟩ := a.exists_index
    have hmem : (Term.name (V := Empty) (ns.nonce i.1 i.2)).baseClass ∈ (combinationNonce ns a).composeFactors := by
      rw [combinationNonce,Combination.named_nonce_factors]
      exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩
    exact False.elim (frame_nonce_factor_not_deducible ns swap left right r hr
      (ns.nonce_mem_nonceNames i.1 i.2) _ hmem he.symm)
  | mixed u v a =>
    obtain ⟨i,hi⟩ := a.exists_index
    have hmem : (Term.name (V := Empty) (ns.nonce i.1 i.2)).baseClass ∈
        (Term.binary .compose ((frame ns swap left right).eval u) (combinationNonce ns a)).composeFactors := by
      apply Multiset.mem_add.mpr
      right
      rw [combinationNonce,Combination.named_nonce_factors]
      exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩
    exact False.elim (frame_nonce_factor_not_deducible ns swap left right r hr
      (ns.nonce_mem_nonceNames i.1 i.2) _ hmem he.symm)

/-- Every public ciphertext constructor with minimum children is minimum in
the initial historical frame. No freshness, observation or normality premise
is required. Public nonce provenance excludes cheaper honest/mixed assemblies. -/
theorem minimum_penc_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b c : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hc : MinimalRecipe ns.restricted (frame ns swap left right).value c) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.ternary .penc a b c) := by
  have hp : (Term.ternary .penc a b c).Public ns.restricted := ⟨ha.isPublic,hb.isPublic,hc.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  obtain ⟨t,rfl,_,hpub,_,hkeypub,_,hkey,hnonce,hmessage⟩ :=
    minimum_ciphertext_grouping ns swap left right ns.restricted m hm he.symm
  obtain ⟨r,p,hg⟩ := t.group.constructed_of_public_nonce ns swap left right b
    (hb.isPublic.of_subset (fun _ h => Finset.mem_union_right _ h)) hnonce
  have hbudget := t.key_group_budget
  rw [hg] at hbudget hpub hnonce hmessage
  have hkeysize := ha.least t.keyRecipe hkeypub hkey.symm
  have hnoncesize := hb.least r hpub.1 hnonce.symm
  have hmessagesize := hc.least p hpub.2 hmessage.symm
  exact hm.of_equivalent_size hp he (by
    simp only [CiphertextGroup.budget,Term.nodeCount] at hbudget ⊢
    omega)

end ExplainableCrypto.Helios.Symbolic.Historical.General
