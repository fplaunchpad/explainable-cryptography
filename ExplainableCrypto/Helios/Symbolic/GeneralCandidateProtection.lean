import ExplainableCrypto.Helios.Symbolic.GeneralCandidateFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat} {restricted : Finset Nat}

/-- Literal-bit honest ballots protect names for any protected-name policy. -/
theorem ballot_protected_bits (ns : Names n) (i : Fin 2) (bits : Fin (n + 1) → Constant) :
    (ballot ns i (fun j => .const (bits j))).nonceSafe restricted = true := by
  apply tuple_protected
  intro t ht
  simp only [ballotFields, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | rfl
  · simp [ciphertext, publicKey, Term.nonceSafe]
  · rfl
  · rfl

theorem frame_protected_bits (ns : Names n) (swap : Bool) (left right : BitCandidate n) :
    ∀ h, ((frame ns swap left.substitution right.substitution).value h).nonceSafe restricted = true := by
  intro h
  cases swap <;> fin_cases h
  · rfl
  · exact ballot_protected_bits ns 0 left.bit
  · exact ballot_protected_bits ns 1 right.bit
  · rfl
  · exact ballot_protected_bits ns 0 right.bit
  · exact ballot_protected_bits ns 1 left.bit

/-- Arbitrary valid representations need not be syntactically protected. Public
recipes nevertheless have E-equal protected values via the literal-bit frame. -/
theorem frame_recipe_protected_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3)
    (hp : recipe.Public restricted) :
    ∃ t : Ground, EqE ((frame ns swap left right).eval recipe) t ∧ t.nonceSafe restricted = true := by
  obtain ⟨a, b, hframe⟩ := frame_bit_representatives ns swap left right
  exact ⟨(frame ns swap a.substitution b.substitution).eval recipe,
    recipe.subst_congr _ _ hframe,
    recipe.nonce_safe_subst _ (hp.nonce_safe recipe) (frame_protected_bits ns swap a b)⟩

theorem frame_nonce_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3)
    (hp : recipe.Public restricted) {name : Nat} (hn : name ∈ restricted) :
    ¬ EqE ((frame ns swap left right).eval recipe) (.name name) := by
  obtain ⟨t, he, ht⟩ := frame_recipe_protected_value ns swap left right recipe hp
  intro h
  exact nonce_safe_not_eqE_name ht hn (he.symm.trans h)

/-- Composed targets may have arbitrary reducible remainders; a protected name
factor suffices after transporting the recipe to an E-equal protected value. -/
theorem frame_nonce_factor_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3)
    (hp : recipe.Public restricted) {name : Nat} (hn : name ∈ restricted)
    (target : Ground) (hfactor : (Term.name (V := Empty) name).baseClass ∈ target.composeFactors) :
    ¬ EqE ((frame ns swap left right).eval recipe) target := by
  obtain ⟨t, he, ht⟩ := frame_recipe_protected_value ns swap left right recipe hp
  intro h
  exact nonce_safe_not_eqE_name_factor ht hn hfactor (he.symm.trans h)

end ExplainableCrypto.Helios.Symbolic.Historical.General
