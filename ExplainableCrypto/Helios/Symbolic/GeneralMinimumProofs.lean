import ExplainableCrypto.Helios.Symbolic.ProofMinimumTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem minimum_decryption_no_match (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (a b : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.binary .dec a b))
    (out : Ground) :
    ¬ DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) out := by
  have hb := hm.subterm (.binaryRight .dec a .hole)
  exact hm.no_decryption_match_of_certificates
    (minimum_pair_and_ciphertext_origins ns swap left right restricted b hb).2 out

theorem minimum_proof_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (recipe : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value recipe)
    {k s m c : Ground} (he : EqE ((frame ns swap left right).eval recipe) (.spk k s m c)) :
    (∃ a b c d, recipe = .spk a b c d) ∨ ∃ v, ProjectionChain v recipe :=
  (frame ns swap left right).minimum_proof_origin_of_origins restricted
    (fun r hm _ _ he => minimum_pair_origin ns swap left right restricted r hm he)
    (fun a b hm out => minimum_decryption_no_match ns swap left right restricted a b hm out)
    recipe hm he

theorem key_projection_chain_not_spk (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) {recipe : Recipe 3} (h : ProjectionChain 0 recipe)
    (k s m c : Ground) : ¬ EqE ((frame ns swap left right).eval recipe) (.spk k s m c) := by
  cases h with
  | handle => exact pk_not_eqE_spk _ _ _ _ _
  | step f hf h =>
    intro he
    obtain ⟨x, y, hp, _⟩ := he.projection_spk_inversion hf
    exact h.not_pair_of_handle (σ := (frame ns swap left right).value)
      (fun _ _ => pk_not_eqE_pair _ _ _) x y hp.sound

/-- All borrowed minimum proof values have actual honest proof positions. -/
theorem minimum_proof_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (recipe : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value recipe)
    {k s m c : Ground} (he : EqE ((frame ns swap left right).eval recipe) (.spk k s m c)) :
    ProofRecipeForm n recipe := by
  rcases minimum_proof_origin ns swap left right restricted recipe hm he with hc | ⟨v, hc⟩
  · exact Or.inl hc
  · fin_cases v
    · exact False.elim (key_projection_chain_not_spk ns swap left right hc k s m c he)
    · rcases voter_projection_proof_origin ns swap left right 0 hc he with ⟨j, hr, _⟩ | ⟨hr, _⟩
      · exact Or.inr (Or.inl ⟨0, j, hr⟩)
      · exact Or.inr (Or.inr ⟨0, hr⟩)
    · rcases voter_projection_proof_origin ns swap left right 1 hc he with ⟨j, hr, _⟩ | ⟨hr, _⟩
      · exact Or.inr (Or.inl ⟨1, j, hr⟩)
      · exact Or.inr (Or.inr ⟨1, hr⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General
