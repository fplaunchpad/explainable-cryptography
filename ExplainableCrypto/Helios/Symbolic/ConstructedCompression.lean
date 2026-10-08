import ExplainableCrypto.Helios.Symbolic.HonestProductMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A nontrivial constructed-only tree saves at least one key occurrence
when compressed. Nonce/message trees retain all their syntax occurrences. -/
theorem CiphertextAssembly.constructed_mul_compression_smaller (a b : CiphertextAssembly n)
    {r p : Recipe 3} (hg : (a.mul b).group = .constructed r p) :
    (Term.ternary .penc (a.mul b).keyRecipe r p).nodeCount < (a.mul b).recipe.nodeCount := by
  have ha := a.key_group_budget
  have hb := b.key_group_budget
  have hk := b.keyRecipe.nodeCount_pos
  cases hga : a.group <;> cases hgb : b.group <;>
    simp only [CiphertextAssembly.group,hga,hgb,CiphertextGroup.merge] at hg <;> cases hg
  rw [hga] at ha
  rw [hgb] at hb
  simp only [CiphertextGroup.budget,CiphertextAssembly.keyRecipe,CiphertextAssembly.recipe,Term.nodeCount] at ha hb ⊢
  omega

/-- The selected key and public grouped components form a public ciphertext
constructor under the original caller policy. -/
theorem CiphertextAssembly.constructed_compression_public (t : CiphertextAssembly n)
    {restricted : Finset Nat} (hp : t.recipe.Public restricted) {r p : Recipe 3}
    (hg : t.group = .constructed r p) :
    (Term.ternary .penc t.keyRecipe r p).Public restricted := by
  have hgp := t.group_public hp
  rw [hg] at hgp
  exact ⟨t.keyRecipe_public hp,hgp⟩

/-- Coherent same-key fusion evaluates to the selected-key grouped
constructor. No source minimum-size or freshness premise is needed. -/
theorem CiphertextAssembly.constructed_compression_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    {r p : Recipe 3} (hg : t.group = .constructed r p)
    (hc : t.Coherent (frame ns swap left right)) :
    EqE ((frame ns swap left right).eval t.recipe)
      ((frame ns swap left right).eval (.ternary .penc t.keyRecipe r p)) := by
  have h := t.grouped_value ns swap left right _ (t.key_agreement_of_coherent ns swap left right hc)
  simpa only [hg,CiphertextGroup.nonce,CiphertextGroup.message,Frame.eval,Term.subst] using h

/-- A minimum coherent constructed-only assembly cannot have a multiplication
root: compressing it would give a strictly smaller public equivalent. -/
theorem minimum_constructed_group_recipe (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value t.recipe)
    {r p : Recipe 3} (hg : t.group = .constructed r p)
    (hc : t.Coherent (frame ns swap left right)) :
    t.recipe = .ternary .penc t.keyRecipe r p := by
  cases t with
  | constructed k nr m => cases hg; rfl
  | honest i => cases hg
  | mul a b =>
    exact False.elim (hm.no_smaller ((a.mul b).constructed_compression_public hm.isPublic hg)
      ((a.mul b).constructed_compression_value ns swap left right hg hc)
      (a.constructed_mul_compression_smaller b hg))

/-- A minimum ciphertext whose nonce is public must be a raw penc, rather
than an honest or mixed assembly or a nontrivial public ciphertext product. -/
theorem minimum_ciphertext_public_nonce_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t nonce : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value t)
    (hn : nonce.Public ns.nonceNames) {key message : Ground}
    (he : EqE ((frame ns swap left right).eval t)
      (.ternary .penc key ((frame ns swap left right).eval nonce) message)) :
    ∃ k r p, t = .ternary .penc k r p := by
  obtain ⟨a,rfl,hkey,_,_,_,_,_,hnonce,_⟩ := minimum_ciphertext_grouping ns swap left right ns.restricted t hm he
  obtain ⟨r,p,hg⟩ := a.group.constructed_of_public_nonce ns swap left right nonce hn hnonce
  exact ⟨a.keyRecipe,r,p,minimum_constructed_group_recipe ns swap left right a hm hg
    (a.coherent_of_key_agreement ns swap left right key hkey)⟩

/-- Coherence in both worlds makes strict constructed compression a shared
equivalent. A supplied smaller-recipe hypothesis then yields its shared minimum. -/
theorem constructed_mul_shared_of_coherent_both (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (a b : CiphertextAssembly n)
    (hp : (a.mul b).recipe.Public ns.restricted) {r p : Recipe 3}
    (hg : (a.mul b).group = .constructed r p)
    (hc : (a.mul b).Coherent (frame ns swap left right))
    (hc' : (a.mul b).Coherent (frame ns swap' left right))
    (hsmall : ∀ s : Recipe 3, s.Public ns.restricted → s.nodeCount < (a.mul b).recipe.nodeCount →
      Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) s) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (a.mul b).recipe := by
  exact (hsmall _ ((a.mul b).constructed_compression_public hp hg)
    (a.constructed_mul_compression_smaller b hg)).of_shared_equivalent
      ((a.mul b).constructed_compression_value ns swap left right hg hc)
      ((a.mul b).constructed_compression_value ns swap' left right hg hc')

/-- Smaller observations transfer all internal key agreements. Both the
observation and smaller shared-minimum premises remain explicit here. -/
theorem constructed_mul_shared_of_smaller_observations (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (a b : CiphertextAssembly n)
    (hp : (a.mul b).recipe.Public ns.restricted) {r p : Recipe 3}
    (hg : (a.mul b).group = .constructed r p)
    (hc : (a.mul b).Coherent (frame ns swap left right))
    (hobs : (frame ns swap left right).ObservationsBelow (frame ns swap' left right) (a.mul b).recipe.nodeCount)
    (hsmall : ∀ s : Recipe 3, s.Public ns.restricted → s.nodeCount < (a.mul b).recipe.nodeCount →
      Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) s) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (a.mul b).recipe :=
  constructed_mul_shared_of_coherent_both ns swap swap' left right a b hp hg hc
    (((a.mul b).coherent_transfer _ _ hp hobs).mp hc) hsmall

end ExplainableCrypto.Helios.Symbolic.Historical.General
