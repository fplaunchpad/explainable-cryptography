import ExplainableCrypto.Helios.Symbolic.MinimumObservationAssembly

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum public key argument gives a minimum constructed key. The full
restriction prevents a shorter alias through the election-key handle. -/
theorem minimum_pk_of_child (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.unary .pk a) := by
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value)
    (.unary .pk a) ha.isPublic
  rcases minimum_public_key_form ns swap left right ns.restricted m hm he.symm with
    rfl | ⟨b, rfl⟩
  · exact False.elim (constructed_key_not_election_key ns swap left right a ha.isPublic he)
  · have hle := ha.least b hm.isPublic ((EqE.pk_iff _ _).mp he)
    exact hm.of_equivalent_size ha.isPublic he (by simp only [Term.nodeCount]; omega)

/-- Initial-frame partial values have only explicit minimum constructor origins. -/
theorem minimum_partial_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.binary .partialDecrypt a b) := by
  have hp : (Term.binary .partialDecrypt a b).Public ns.restricted := ⟨ha.isPublic, hb.isPublic⟩
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  obtain ⟨u, v, rfl⟩ := minimum_partial_decryption_form ns swap left right ns.restricted m hm he.symm
  have hargs := (EqE.partialDecrypt_iff _ _ _ _).mp he
  have hua := ha.least u hm.isPublic.1 hargs.1
  have hvb := hb.least v hm.isPublic.2 hargs.2
  exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)

/-- Public nonce recipes exclude honest proof aliases; explicit proof minima
then retain all four independently minimum components. -/
theorem minimum_spk_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b c d : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hc : MinimalRecipe ns.restricted (frame ns swap left right).value c)
    (hd : MinimalRecipe ns.restricted (frame ns swap left right).value d) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.spk a b c d) := by
  have hp : (Term.spk a b c d).Public ns.restricted := ⟨ha.isPublic, hb.isPublic, hc.isPublic, hd.isPublic⟩
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  have hnonce := hb.isPublic.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
  rcases minimum_proof_form ns swap left right ns.restricted m hm he.symm with
    ⟨u, v, w, x, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, rfl⟩
  · have hargs := (EqE.spk_iff _ _ _ _ _ _ _ _).mp he
    have hu := ha.least u hm.isPublic.1 hargs.1
    have hv := hb.least v hm.isPublic.2.1 hargs.2.1
    have hw := hc.least w hm.isPublic.2.2.1 hargs.2.2.1
    have hx := hd.least x hm.isPublic.2.2.2 hargs.2.2.2
    exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)
  · exact False.elim (constructed_proof_not_component ns swap left right a b c d hnonce i j
      (he.trans (component_proof_recipe_value ns swap left right i j)))
  · exact False.elim (constructed_proof_not_aggregate ns swap left right a b c d hnonce i
      (he.trans (aggregate_proof_recipe_value ns swap left right i)))

/-- A semantically stuck projection of a minimum child is itself minimum. -/
theorem minimum_stuck_projection_of_child (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (f : Unary) (hf : f = .fst ∨ f = .snd)
    (a : Recipe 3) (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hn : ∀ x y, ¬ EqE ((frame ns swap left right).eval a) (.binary .pair x y)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.unary f a) := by
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) (.unary f a) ha.isPublic
  obtain ⟨b, rfl, hnb⟩ := minimum_stuck_projection_form ns swap left right ns.restricted m hm f hf hn he.symm
  have hab := ((EqE.projection_iff_of_no_pair f f hf hf _ _ hn hnb).mp he).2
  have hle := ha.least b hm.isPublic hab
  exact hm.of_equivalent_size ha.isPublic he (by simp only [Term.nodeCount]; omega)

/-- Failure means absence of every reachable E5/E6 match, not failed raw matching. -/
theorem minimum_stuck_decryption_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hn : ∀ m, ¬ DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) m) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.binary .dec a b) := by
  have hp : (Term.binary .dec a b).Public ns.restricted := ⟨ha.isPublic, hb.isPublic⟩
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  obtain ⟨u, v, rfl, hnm⟩ := minimum_stuck_decryption_form ns swap left right ns.restricted m hm hn he.symm
  have hargs := (EqE.decryption_iff_of_no_match _ _ _ _ hn hnm).mp he
  have hu := ha.least u hm.isPublic.1 hargs.1
  have hv := hb.least v hm.isPublic.2 hargs.2
  exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)

/-- Stuck proof checks retain all three minimum children in their size bound. -/
theorem minimum_stuck_check_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b c : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hc : MinimalRecipe ns.restricted (frame ns swap left right).value c)
    (hn : ¬ ProofCheckMatch ((frame ns swap left right).eval a)
      ((frame ns swap left right).eval b) ((frame ns swap left right).eval c)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value (.ternary .checkspk a b c) := by
  have hp : (Term.ternary .checkspk a b c).Public ns.restricted := ⟨ha.isPublic, hb.isPublic, hc.isPublic⟩
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  obtain ⟨u, v, w, rfl⟩ := minimum_stuck_check_form ns swap left right ns.restricted m hm hn he.symm
  have hargs := (EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hn (hm.no_proof_check_match u v w)).mp he
  have hu := ha.least u hm.isPublic.1 hargs.1
  have hv := hb.least v hm.isPublic.2.1 hargs.2.1
  have hw := hc.least w hm.isPublic.2.2 hargs.2.2
  exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)

end ExplainableCrypto.Helios.Symbolic.Historical.General
