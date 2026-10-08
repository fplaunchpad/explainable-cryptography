import ExplainableCrypto.Helios.Symbolic.DecryptCheckCipherMulTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Grouping an assembly as honest cannot erase any constructed contribution.
The raw recipe is exactly the recorded honest selector combination. -/
theorem CiphertextAssembly.recipe_of_honest_group (t : CiphertextAssembly n)
    {a : Combination (HonestIndex n)} (hg : t.group = .honest a) :
    t.recipe = combinationRecipe a := by
  induction t generalizing a with
  | constructed k r p => cases hg
  | honest i => cases hg; rfl
  | mul t u it iu =>
    cases ht : t.group <;> cases hu : u.group <;>
      simp only [CiphertextAssembly.group,ht,hu,CiphertextGroup.merge] at hg <;> cases hg
    exact congrArg₂ (Term.binary .mul) (it ht) (iu hu)

/-- A selector at index j costs j+2 nodes; each occurrence pays j+3 in the
node-count-plus-one accounting for a nonempty binary multiplication tree. -/
theorem combinationRecipe_nodeCount (a : Combination (HonestIndex n)) :
    (combinationRecipe a).nodeCount+1 = (a.indices.map (fun i => i.2.val+3)).sum := by
  induction a with
  | leaf i => simp [combinationRecipe,Combination.evaluate,Combination.indices,Term.project_nodeCount,Term.nodeCount]; omega
  | mul a b ia ib =>
    simp only [combinationRecipe,Combination.evaluate,Term.nodeCount,Combination.indices,
      Multiset.map_add,Multiset.sum_add] at *
    omega

/-- Equal indexed occurrence bags determine exact honest recipe size. -/
theorem combinationRecipe_nodeCount_eq {a b : Combination (HonestIndex n)}
    (h : a.indices = b.indices) : (combinationRecipe a).nodeCount = (combinationRecipe b).nodeCount := by
  have ha := combinationRecipe_nodeCount a
  have hb := combinationRecipe_nodeCount b
  rw [h] at ha
  omega

/-- Any globally minimum equivalent of an honest-only product has only
honest selectors and exactly the original fresh nonce-index occurrence bag. -/
theorem minimum_honest_combination_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (a : Combination (HonestIndex n))
    (he : EqE ((frame ns swap left right).eval r) ((frame ns swap left right).eval (combinationRecipe a))) :
    ∃ b, r = combinationRecipe b ∧ b.indices = a.indices := by
  obtain ⟨t,rfl,_,hpub,_,_,_,_,hnonce,hmessage⟩ := minimum_ciphertext_grouping ns swap left right ns.restricted r hm
    (he.trans (combination_value ns swap left right a))
  have hp := hpub.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
  have obs := (CiphertextGroup.components_eq_iff ns hf swap left right t.group (.honest a)
    hp trivial).mp ⟨hnonce,hmessage⟩
  cases hg : t.group with
  | constructed r p => simp only [hg,CiphertextGroup.Observation] at obs
  | mixed r p b => simp only [hg,CiphertextGroup.Observation] at obs
  | honest b => exact ⟨b,t.recipe_of_honest_group hg,by simpa only [hg,CiphertextGroup.Observation] using obs⟩

/-- Every nonempty combination of fresh honest ciphertext selectors is
globally minimum among all public recipes in either initial assignment. -/
theorem minimum_honest_combination (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a : Combination (HonestIndex n)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (combinationRecipe a) := by
  have hp := combinationRecipe_public ns.restricted a
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  obtain ⟨b,rfl,hb⟩ := minimum_honest_combination_origin ns hf swap left right m hm a he.symm
  exact hm.of_equivalent_size hp he (Nat.le_of_eq (combinationRecipe_nodeCount_eq hb.symm))

/-- Honest-only products need no replacement to be shared: their existing
syntax is minimum in the source and identical in every destination. -/
theorem honest_combination_shared (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a : Combination (HonestIndex n))
    (ψ : Frame ns.restricted 3) : Frame.SharedMinimum (frame ns swap left right) ψ (combinationRecipe a) :=
  .of_minimal (minimum_honest_combination ns hf swap left right a)

/-- An assembly recorded as honest is already minimum. Nonminimum remaining
ciphertext products must contain a public constructed contribution. -/
theorem minimum_assembly_of_honest_group (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    {a : Combination (HonestIndex n)} (hg : t.group = .honest a) :
    MinimalRecipe ns.restricted (frame ns swap left right).value t.recipe := by
  rw [t.recipe_of_honest_group hg]
  exact minimum_honest_combination ns hf swap left right a

/-- A nonminimum ciphertext-valued product with minimum children has an exact
coherent assembly with a public constructed contribution. Honest-only groups
are ruled out by the global minimum theorem, not by an attacker restriction. -/
theorem nonminimum_ciphertext_product_public_group (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hm : ¬ MinimalRecipe ns.restricted (frame ns swap left right).value (.binary .mul a b))
    (hv : ((frame ns swap left right).eval (.binary .mul a b)).CiphertextValue) :
    ∃ t : CiphertextAssembly n, t.recipe = .binary .mul a b ∧
      t.recipe.Public ns.restricted ∧ t.Coherent (frame ns swap left right) ∧
      ((∃ r p, t.group = .constructed r p) ∨ (∃ r p c, t.group = .mixed r p c)) := by
  obtain ⟨k,nr,m,he⟩ := hv
  obtain ⟨_,_,_,_,hea,heb,_,_⟩ := he.mul_penc_inversion
  obtain ⟨u,hu⟩ := assembly_of_ciphertext_syntax ns swap left right
    (minimum_ciphertext_syntax ns swap left right ns.restricted a ha hea) hea
  obtain ⟨v,hv⟩ := assembly_of_ciphertext_syntax ns swap left right
    (minimum_ciphertext_syntax ns swap left right ns.restricted b hb heb) heb
  let t := CiphertextAssembly.mul u v
  have ht : t.recipe = .binary .mul a b := by simp only [t,CiphertextAssembly.recipe,hu,hv]
  have hcoh : t.Coherent (frame ns swap left right) :=
    (t.coherent_iff_ciphertext_value ns swap left right).mpr ⟨k,nr,m,by simpa only [ht] using he⟩
  refine ⟨t,ht,ht ▸ ⟨ha.isPublic,hb.isPublic⟩,hcoh,?_⟩
  cases hg : t.group with
  | constructed r p => exact Or.inl ⟨r,p,rfl⟩
  | mixed r p c => exact Or.inr ⟨r,p,c,rfl⟩
  | honest c =>
    have hmin := minimum_assembly_of_honest_group ns hf swap left right t hg
    exact False.elim (hm (ht ▸ hmin))

end ExplainableCrypto.Helios.Symbolic.Historical.General
