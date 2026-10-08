import ExplainableCrypto.Helios.Symbolic.MixedCompressionCosts

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat} {restricted : Finset Nat}

/-- Any honest contribution binds the common key to the public key. This
does not apply to a constructed-only group with an unrelated coherent key. -/
theorem CiphertextAssembly.key_agreement_public_key_of_nonconstructed
    (ns : Names n) (φ : Frame restricted handles) (t : CiphertextAssembly n handles) {key : Ground}
    (hk : t.KeyAgreement ns φ key)
    (hn : ∀ r p, t.group ≠ .constructed r p) : EqE (publicKey ns) key := by
  induction t with
  | constructed k r p => exact False.elim (hn r p rfl)
  | honest i => exact hk
  | mul a b ia ib =>
    by_cases ha : ∃ r p, a.group = .constructed r p
    · obtain ⟨r,p,ha⟩ := ha
      apply ib hk.2
      intro s q hb
      apply hn (.binary .compose r s) (.binary .add p q)
      simp only [CiphertextAssembly.group,ha,hb,CiphertextGroup.merge]
    · exact ia hk.1 (fun r p h => ha ⟨r,p,h⟩)

/-- A coherent mixed tree equals its grouped public-key constructor times
the exact honest combination, preserving all nonce and payload contributions. -/
theorem CiphertextAssembly.mixed_compression_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    {r p : Recipe 3} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hc : t.Coherent (frame ns swap left right)) :
    EqE ((frame ns swap left right).eval t.recipe)
      ((frame ns swap left right).eval (mixedCombinationRecipe r p a)) := by
  have hk := t.key_agreement_of_coherent ns swap left right hc
  have hkey := t.key_agreement_public_key_of_nonconstructed ns _ hk (by
    intro u v he
    rw [hg] at he
    cases he)
  have hv := t.grouped_value ns swap left right (publicKey ns)
    (t.key_agreement_congr ns _ hk hkey.symm)
  have he := mixedCombination_value ns swap left right r p a
  exact hv.trans (by simpa only [hg,CiphertextGroup.nonce,CiphertextGroup.message] using he.symm)

/-- A minimum mixed assembly has exactly one public constructor occurrence.
Two or more would give a strictly smaller public grouped equivalent. -/
theorem minimum_mixed_constructedCount_eq_one (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value t.recipe)
    {r p : Recipe 3} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hc : t.Coherent (frame ns swap left right)) : t.constructedCount = 1 := by
  have hp := t.mixed_constructedCount_pos hg
  by_contra hn
  exact hm.no_smaller (t.mixed_compression_public hm.isPublic hg)
    (t.mixed_compression_value ns swap left right hg hc) (t.mixed_compression_smaller hg (by omega))

/-- Regrouping a minimum mixed assembly attains exactly the same minimum
size. The original syntactic position of its sole constructor need not be fixed. -/
theorem minimum_mixed_grouped_representative (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value t.recipe)
    {r p : Recipe 3} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hc : t.Coherent (frame ns swap left right)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (mixedCombinationRecipe r p a) ∧
      (mixedCombinationRecipe r p a).nodeCount = t.recipe.nodeCount := by
  have hp := t.mixed_compression_public hm.isPublic hg
  have he := t.mixed_compression_value ns swap left right hg hc
  have hcount := minimum_mixed_constructedCount_eq_one ns swap left right t hm hg hc
  have hcst := t.mixed_compression_cost hg
  have hle := hm.least _ hp he
  exact ⟨hm.of_equivalent_size hp he.symm (by omega),by omega⟩

/-- Every minimum equivalent of a public mixed combination has one constructed
occurrence, the same honest index bag, an equal public nonce and an equal
zero-padded payload. Its own grouped representative attains the same size. -/
theorem minimum_mixed_combination_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r p : Recipe 3)
    (hr : r.Public ns.nonceNames) (hp : p.Public ns.nonceNames) (a : Combination (HonestIndex n))
    (m : Recipe 3) (hm : MinimalRecipe ns.restricted (frame ns swap left right).value m)
    (he : EqE ((frame ns swap left right).eval m)
      ((frame ns swap left right).eval (mixedCombinationRecipe r p a))) :
    ∃ t : CiphertextAssembly n, ∃ s q b,
      t.recipe=m ∧ t.group=.mixed s q b ∧ t.constructedCount=1 ∧
      b.indices=a.indices ∧ EqE ((frame ns swap left right).eval s) ((frame ns swap left right).eval r) ∧
      EqE ((frame ns swap left right).eval (.binary .add q (.const .zero)))
        ((frame ns swap left right).eval (.binary .add p (.const .zero))) ∧
      (mixedCombinationRecipe s q b).nodeCount=m.nodeCount := by
  obtain ⟨t,rfl,hkey,hpub,_,_,_,_,hnonce,hmessage⟩ := minimum_ciphertext_grouping ns swap left right
    ns.restricted m hm (he.trans (mixedCombination_value ns swap left right r p a))
  have hpub' := hpub.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
  have obs := (CiphertextGroup.components_eq_iff ns hf swap left right t.group (.mixed r p a)
    hpub' ⟨hr,hp⟩).mp ⟨hnonce,hmessage⟩
  have hc := t.coherent_of_key_agreement ns swap left right _ hkey
  cases hg : t.group with
  | constructed s q => simp only [hg,CiphertextGroup.Observation] at obs
  | honest b => simp only [hg,CiphertextGroup.Observation] at obs
  | mixed s q b =>
    simp only [hg,CiphertextGroup.Observation] at obs
    exact ⟨t,s,q,b,rfl,hg,minimum_mixed_constructedCount_eq_one ns swap left right t hm hg hc,
      obs.1,obs.2.1,obs.2.2,(minimum_mixed_grouped_representative ns swap left right t hm hg hc).2⟩

/-- The two strict smaller-minimum induction hypotheses close every mixed
assembly containing at least two public constructor occurrences. -/
theorem mixed_compression_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    (hp : t.recipe.Public ns.restricted) {r p : Recipe 3} {a : Combination (HonestIndex n)}
    (hg : t.group = .mixed r p a) (hc : t.Coherent (frame ns swap left right))
    (hcount : 2 ≤ t.constructedCount)
    (hforward : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right) t.recipe.nodeCount)
    (hreverse : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right) t.recipe.nodeCount) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) t.recipe := by
  have hobs := observationsBelow_of_two_way_minima ns hf swap swap' left right _ hforward hreverse
  have hc' := (t.coherent_transfer _ _ hp hobs).mp hc
  exact (hforward _ (t.mixed_compression_public hp hg) (t.mixed_compression_smaller hg hcount)).of_shared_equivalent
    (t.mixed_compression_value ns swap left right hg hc)
    (t.mixed_compression_value ns swap' left right hg hc')

/-- A minimum nonce and an atomic public payload attain the global mixed
minimum: every competitor pays the same honest bag, the nonce minimum and at
least one payload node. The honest combination is arbitrary and nonempty. -/
theorem minimum_mixed_of_minimum_nonce_atomic_payload (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r p : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (hp : p.Public ns.restricted) (hsize : p.nodeCount=1) (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (mixedCombinationRecipe r p a) := by
  have hpublic := mixedCombination_public r p hr.isPublic hp a
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hpublic
  have hsub : ns.nonceNames ⊆ ns.restricted := fun _ h => Finset.mem_union_right _ h
  obtain ⟨t,s,q,b,ht,hg,_,hi,hn,_,hcst⟩ := minimum_mixed_combination_origin ns hf swap left right
    r p (hr.isPublic.of_subset hsub) (hp.of_subset hsub) a m hm he.symm
  have hs := t.group_public (ht.symm ▸ hm.isPublic)
  rw [hg] at hs
  have hnonce := hr.least s hs.1 hn.symm
  have hhonest := combinationRecipe_nodeCount_eq hi
  have hq := q.nodeCount_pos
  apply hm.of_equivalent_size hpublic he
  simp only [mixedCombinationRecipe,Term.nodeCount] at hcst ⊢
  omega

end ExplainableCrypto.Helios.Symbolic.Historical.General
