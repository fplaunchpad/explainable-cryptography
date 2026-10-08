import ExplainableCrypto.Helios.Symbolic.StuckDestructorOrigins
import ExplainableCrypto.Helios.Symbolic.MinimumDestructorSPOT

namespace ExplainableCrypto.Helios.Symbolic.StuckDestructorSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev reveal (t : Ground) : Ground := .unary .fst (.binary .pair t (.const .bottom))
abbrev projection : Recipe 3 := .unary .fst (.var 0)
abbrev decryption (a b : Nat) : Recipe 3 := .binary .dec (.name a) (.name b)

private theorem named_value_no_pair {a : Ground} {name : Nat} (he : EqE a (.name name)) :
    ∀ x y, ¬ EqE a (.binary .pair x y) := by
  intro x y hp
  obtain ⟨_, _, hh, _⟩ := (hp.symm.trans he).passive_binary_irreducible_shape (Or.inl rfl) (name_irreducible name)
  cases hh

private theorem named_value_no_match (a : Ground) {b : Ground} {name : Nat} (he : EqE b (.name name)) :
    ∀ m, ¬ DecryptionMatch a b m := by
  rintro m ⟨k, r, _, hb⟩
  obtain ⟨_, _, _, hh, _⟩ := (hb.sound.symm.trans he).penc_irreducible_shape (name_irreducible name)
  cases hh

/-- Reductions inside stuck arguments preserve the independently chosen names.
Neither the selector nor dec argument order is erased by the model. -/
theorem reducible_stuck_values :
    EqE (.unary .fst (reveal (.name 40))) (.unary .fst (.name 40)) ∧
    EqE (.binary .dec (reveal (.name 40)) (reveal (.name 50))) (.binary .dec (.name 40) (.name 50)) ∧
    ¬ EqE (.unary .fst (reveal (.name 40))) (.unary .snd (.name 40)) ∧
    ¬ EqE (.binary .dec (reveal (.name 40)) (reveal (.name 50))) (.binary .dec (.name 50) (.name 40)) := by
  have h40 : EqE (reveal (.name 40)) (.name 40) := (RootStep.fst _ _).sound
  have h50 : EqE (reveal (.name 50)) (.name 50) := (RootStep.fst _ _).sound
  refine ⟨.unary .fst h40, .binary .dec h40 h50, ?_, ?_⟩
  · intro he
    have hf := ((EqE.projection_iff_of_no_pair .fst .snd (Or.inl rfl) (Or.inr rfl) _ _
      (named_value_no_pair h40) (named_value_no_pair (.refl _))).mp he).1
    cases hf
  · intro he
    have ha := ((EqE.decryption_iff_of_no_match _ _ _ _ (named_value_no_match _ h50)
      (named_value_no_match _ (.refl _))).mp he).1
    have h := (EqE.name_iff 40 50).mp (h40.symm.trans ha)
    omega

/-- The no-pair mutation's input-0 witness: successful projections forget the
unused pair member. Equal selected values do not make the pair arguments equal. -/
theorem matching_projection_not_injective :
    EqE (.unary .fst (.binary .pair (.const .one) (.const .zero) : Ground))
      (.unary .fst (.binary .pair (.const .one) (.const .one))) ∧
    ¬ EqE (.binary .pair (.const .one) (.const .zero) : Ground)
      (.binary .pair (.const .one) (.const .one)) := by
  refine ⟨(RootStep.fst _ _).sound.trans (RootStep.fst _ _).sound.symm, ?_⟩
  intro he
  exact zero_not_one ((EqE.pair_iff _ _ _ _).mp he).2

abbrev cipher (nonce : Nat) : Ground := keyCiphertext (.name 40) (.name nonce) (.const .zero)

/-- E5 and E6 can expose the same plaintext from distinct nonce-bound
ciphertexts. This is the input-0 no-match mutation, with an E6 companion. -/
theorem matching_decryption_not_injective :
    EqE (.binary .dec (.name 40) (cipher 50)) (.binary .dec (.name 40) (cipher 51)) ∧
    EqE (.binary .dec (.binary .partialDecrypt (.name 40) (cipher 50)) (cipher 50)) (.const .zero) ∧
    ¬ EqE (cipher 50) (cipher 51) := by
  refine ⟨(RootStep.decrypt _ _ _).sound.trans (RootStep.decrypt _ _ _).sound.symm,
    (RootStep.partial_decrypt _ _ _).sound, ?_⟩
  intro he
  have h := (EqE.name_iff 50 51).mp ((EqE.penc_iff _ _ _ _ _ _).mp he).2.1
  omega

/-- A stuck fst of the public election-key handle is an exact two-node minimum
in every valid candidate assignment of this actual initial-frame fixture. -/
theorem literal_projection_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty) :
    MinimalRecipe names.restricted (General.frame names swap a b).value projection := by
  have hp : projection.Public names.restricted := trivial
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  obtain ⟨u, rfl, _⟩ := minimum_stuck_projection_form names swap a b names.restricted r hr
    .fst (Or.inl rfl) (fun x y => pk_not_eqE_pair _ x y) he.symm
  refine ⟨hp, fun s hs hes => ?_⟩
  have hle := hr.least s hs (he.symm.trans hes)
  have := u.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- Distinct public names produce exact three-node minimum decryptions, so
stuckness and minimum-size premises hold in real frames. -/
theorem literal_decryption_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (x y : Nat) (hx : x ∉ names.restricted) (hy : y ∉ names.restricted) :
    MinimalRecipe names.restricted (General.frame names swap a b).value (decryption x y) := by
  have hp : (decryption x y).Public names.restricted := ⟨hx, hy⟩
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  obtain ⟨u, v, rfl, _⟩ := minimum_stuck_decryption_form names swap a b names.restricted r hr
    (named_value_no_match (.name x) (EqE.refl (.name y))) he.symm
  refine ⟨hp, fun s hs hes => ?_⟩
  have hle := hr.least s hs (he.symm.trans hes)
  have := u.nodeCount_pos
  have := v.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- A matched target has a literal minimum outside destructor syntax. The
no-match premise is necessary for exact origins, not just for injectivity. -/
theorem stuck_target_premise_required (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.const .zero) ∧
    EqE ((world swap).eval (.const .zero)) (.binary .dec (.name 40) (cipher 50)) ∧
    EqE ((world swap).eval (.const .zero)) (.unary .fst (.binary .pair (.const .zero) (.const .one))) ∧
    ¬ (∃ u v : Recipe 3, (Term.const .zero : Recipe 3) = .binary .dec u v) ∧
    ¬ (∃ u : Recipe 3, (Term.const .zero : Recipe 3) = .unary .fst u) := by
  refine ⟨MinimalRecipe.of_nodeCount_one trivial rfl, (RootStep.decrypt _ _ _).sound.symm,
    (RootStep.fst _ _).sound.symm, ?_, ?_⟩
  · rintro ⟨u, v, h⟩; cases h
  · rintro ⟨u, h⟩; cases h

abbrev wrappedDecryption : Recipe 3 :=
  .unary .fst (.binary .pair (decryption 40 50) (.const .bottom))

/-- A public nonminimum wrapper has a stuck dec value but a different raw head.
Thus value stuckness alone cannot justify exact recipe origins. -/
theorem exact_origin_needs_minimum (swap : Bool) :
    wrappedDecryption.Public names.restricted ∧
    EqE ((world swap).eval wrappedDecryption) ((world swap).eval (decryption 40 50)) ∧
    ¬ (∃ u v : Recipe 3, wrappedDecryption = .binary .dec u v) ∧
    ¬ MinimalRecipe names.restricted (world swap).value wrappedDecryption := by
  have hp : (decryption 40 50).Public names.restricted := by
    change 40 ∉ names.restricted ∧ 50 ∉ names.restricted
    decide
  have he : EqE ((world swap).eval wrappedDecryption) ((world swap).eval (decryption 40 50)) :=
    (RootStep.fst _ _).sound
  refine ⟨⟨hp, trivial⟩, he, ?_, fun hm => hm.no_smaller hp he (by decide)⟩
  rintro ⟨u, v, h⟩
  cases h

/-- A public wrong key cannot decrypt an honest initial ciphertext, even after
arbitrary argument reduction. The honest bit may use a reducible representative. -/
theorem honest_wrong_key_no_match (swap : Bool) (m : Ground) :
    ¬ DecryptionMatch (.name 40)
      (General.ciphertext names 0 (General.choice swap left right 0).value 0) m := by
  rintro ⟨k, nonce, hk, hc⟩
  have hpk := ((EqE.penc_iff _ _ _ _ _ _).mp hc.sound).1
  have hkey : EqE (.name 10 : Ground) k := (EqE.pk_iff _ _).mp hpk
  rcases hk with hk | hk
  · have h := (EqE.name_iff 40 10).mp (hk.sound.trans hkey.symm)
    omega
  · cases ((name_irreducible 40).reducesModulo hk).head_eq

/-- A distinct stuck selector and a distinct decryption argument remain
observable; stuck projection and dec heads are also separated under full E. -/
theorem stuck_outputs_not_constant (swap : Bool) :
    ¬ EqE ((world swap).eval projection) ((world swap).eval (.unary .snd (.var 0))) ∧
    ¬ EqE ((world swap).eval (decryption 40 50)) ((world swap).eval (decryption 40 51)) ∧
    ¬ EqE ((world swap).eval projection) ((world swap).eval (decryption 40 50)) := by
  have hp : ∀ x y, ¬ EqE (publicKey names : Ground) (.binary .pair x y) := fun x y => pk_not_eqE_pair _ x y
  have h50 := named_value_no_match (.name 40) (EqE.refl (.name 50))
  have h51 := named_value_no_match (.name 40) (EqE.refl (.name 51))
  refine ⟨?_, ?_, stuck_projection_not_eqE_decryption .fst (Or.inl rfl) _ _ _ hp h50⟩
  · intro he
    have h := ((EqE.projection_iff_of_no_pair .fst .snd (Or.inl rfl) (Or.inr rfl) _ _ hp hp).mp he).1
    cases h
  · intro he
    have h := (EqE.name_iff 50 51).mp ((EqE.decryption_iff_of_no_match _ _ _ _ h50 h51).mp he).2
    omega

/-- The forward interfaces accept actual minima and reducible supplied targets.
These diagonal equality instances establish inhabitation; the separate unequal
controls establish that the semantics does not equate all stuck outputs. -/
theorem forward_interfaces_inhabited :
    EqE ((General.frame names true left left).eval projection) ((General.frame names true left left).eval projection) ∧
    EqE ((General.frame names true left left).eval (decryption 40 50))
      ((General.frame names true left left).eval (decryption 40 50)) := by
  have hp := literal_projection_minimum false left left
  have hd := literal_decryption_minimum false left left 40 50 (by decide) (by decide)
  have hk : EqE (reveal (publicKey names)) (publicKey names) := (RootStep.fst _ _).sound
  have hnp : ∀ x y, ¬ EqE (reveal (publicKey names)) (.binary .pair x y) :=
    fun x y he => pk_not_eqE_pair _ x y (hk.symm.trans he)
  have h50 : EqE (reveal (.name 50)) (.name 50) := (RootStep.fst _ _).sound
  exact ⟨minimum_stuck_projection_equality_imp names left left projection projection hp hp .fst (Or.inl rfl)
    hnp (.unary .fst hk.symm) (CiphertextObservationSPOT.diagonal_observations _) (.refl _),
    minimum_stuck_decryption_equality_imp names left left (decryption 40 50) (decryption 40 50) hd hd
      (named_value_no_match (.name 40) h50) (.binary .dec (.refl _) h50.symm)
      (CiphertextObservationSPOT.diagonal_observations _) (.refl _)⟩

end ExplainableCrypto.Helios.Symbolic.StuckDestructorSPOT
