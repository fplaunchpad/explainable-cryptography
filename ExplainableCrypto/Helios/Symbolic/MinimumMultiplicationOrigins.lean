import ExplainableCrypto.Helios.Symbolic.MultiplicationOriginTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem mul_origin_with_paths (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    (hd : ∀ a b, r = .binary .dec a b →
      ∀ m, ¬ DecryptionMatch ((frame ns swap' left right).eval a) ((frame ns swap' left right).eval b) m)
    (hp : ∀ f a, r = .unary f a → (f = .fst ∨ f = .snd) →
      ((frame ns swap' left right).eval a).PairValue → ((frame ns swap left right).eval a).PairValue)
    {x y : Ground} (ht : Irreducible (.binary .mul x y)) (he : EqE ((frame ns swap' left right).eval r) (.binary .mul x y)) :
    ∃ a b, r = .binary .mul a b := by
  apply (frame ns swap' left right).normal_mul_form_of_paths r ?_ ?_ ?_ ht he
  · intro v x y _ hv
    fin_cases v
    · exact mul_not_eqE_pk _ _ _ hv.symm
    · obtain ⟨a,b,hpair⟩ := ballot_tail_pair_value ns swap' left right 0 0 (by unfold fieldCount; omega)
      exact mul_not_eqE_passive_binary _ _ _ _ .pair (Or.inl rfl) (hv.symm.trans hpair)
    · obtain ⟨a,b,hpair⟩ := ballot_tail_pair_value ns swap' left right 1 0 (by unfold fieldCount; omega)
      exact mul_not_eqE_passive_binary _ _ _ _ .pair (Or.inl rfl) (hv.symm.trans hpair)
  · intro a b hr out hmatch
    exact False.elim (hd a b hr out hmatch)
  · intro f a hr hf hv
    obtain ⟨u,v,hpair⟩ := hp f a hr hf hv
    subst r
    exact (minimum_successful_projection_form ns swap left right restricted f hf a hm hpair).data_value ns swap' left right

/-- A minimum recipe with an irreducible multiplication value has literal mul
syntax. An irreducible product cannot be a fused ciphertext value. -/
theorem minimum_normal_mul_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {x y : Ground} (ht : Irreducible (.binary .mul x y)) (he : EqE ((frame ns swap left right).eval r) (.binary .mul x y)) :
    ∃ a b, r = .binary .mul a b := by
  apply mul_origin_with_paths ns swap swap left right restricted r hm ?_ ?_ ht he
  · intro a b hr
    subst r
    exact minimum_decryption_no_match ns swap left right restricted a b hm
  · exact fun _ _ _ _ h => h

/-- Smaller public observations exclude a destination irreducible multiplication
value for source minima with another raw head. Destination minimality is absent. -/
theorem minimum_normal_mul_form_after_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount)
    {x y : Ground} (ht : Irreducible (.binary .mul x y)) (he : EqE ((frame ns true left right).eval r) (.binary .mul x y)) :
    ∃ a b, r = .binary .mul a b := by
  apply mul_origin_with_paths ns false true left right ns.restricted r hm ?_ ?_ ht he
  · intro a b hr
    subst r
    exact minimum_decryption_failure_swap ns left right a b hm hobs
  · intro f a hr _ hp
    subst r
    exact (minimum_value_shape_reflection ns left right a (hm.subterm (.unary f .hole))
      (hobs.mono (by simp only [Term.nodeCount]; omega))).1 hp

/-- A supplied multiplication E-value that is not a ciphertext forces raw mul
syntax at a source minimum, without normality assumptions on the supplied value. -/
theorem minimum_non_ciphertext_mul_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {x y : Ground} (he : EqE ((frame ns swap left right).eval r) (.binary .mul x y))
    (hn : ¬ ((frame ns swap left right).eval r).CiphertextValue) :
    ∃ a b, r = .binary .mul a b := by
  obtain ⟨t, ht, hi⟩ := exists_normal_form (.binary .mul x y)
  rcases ht.sound.mul_irreducible_shape hi with ⟨u, v, rfl⟩ | ⟨k, nr, m, rfl⟩
  · exact minimum_normal_mul_form ns swap left right restricted r hm hi (he.trans ht.sound)
  · exact False.elim (hn ⟨k, nr, m, he.trans ht.sound⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General
