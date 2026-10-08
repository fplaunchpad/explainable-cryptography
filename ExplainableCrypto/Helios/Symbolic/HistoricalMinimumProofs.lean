import ExplainableCrypto.Helios.Symbolic.HistoricalMinimumDestructors

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem EqE.decryption_spk_inversion {a b k r m c : Term V}
    (h : EqE (.binary .dec a b) (.spk k r m c)) :
    ∃ p, DecryptionMatch a b p ∧ EqE p (.spk k r m c) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.decryption_cases with ⟨_, _, _, _, ht⟩ | ⟨p, hp, hout⟩
  · obtain ⟨_, _, _, _, hp, _⟩ := hr.spk_components
    cases (ht.symm.trans hp).head_eq
  · exact ⟨p, hp, hout.sound.trans hr.sound.symm⟩

theorem pk_not_eqE_spk (a k r m c : Term V) : ¬ EqE (.unary .pk a) (.spk k r m c) := by
  intro h
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨_, hk, _⟩ := hl.pk_components
  obtain ⟨_, _, _, _, hp, _⟩ := hr.spk_components
  cases (hk.symm.trans hp).head_eq

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {n : Nat}

/-- Exact proof recipe forms: explicit spk, an honest component proof, or its aggregate. -/
def ProofRecipeForm (n : Nat) (r : Recipe 3) : Prop :=
  (∃ a b c d, r = .spk a b c d) ∨
  (∃ i : Fin 2, ∃ j : Fin (n + 1), r = (Term.var i.succ).project (n + 1 + j.val)) ∨
  (∃ i : Fin 2, r = (Term.var i.succ).project (2 * (n + 1)))

theorem minimum_proof_origin (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (recipe : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value recipe)
    {k s m c : Ground} (he : EqE ((frame ns swap left right).eval recipe) (.spk k s m c)) :
    (∃ a b c d, recipe = .spk a b c d) ∨ ∃ v, ProjectionChain v recipe := by
  cases recipe with
  | name a =>
    obtain ⟨_, _, _, _, ht, _⟩ := he.symm.spk_irreducible_shape (name_irreducible a)
    cases ht
  | const d =>
    obtain ⟨_, _, _, _, ht, _⟩ := he.symm.spk_irreducible_shape (constant_irreducible d)
    cases ht
  | var v => exact Or.inr ⟨v, .handle⟩
  | unary f a =>
    have hp (hf : f = .fst ∨ f = .snd) : ∃ v, ProjectionChain v (.unary f a) := by
      obtain ⟨x, y, hx, _⟩ := he.projection_spk_inversion hf
      exact hm.projection_chain_of_pair_origin hf
        (minimum_pair_origin ns swap left right restricted a (hm.subterm (.unary f .hole)) hx.sound)
    cases f with
    | pk => exact False.elim (pk_not_eqE_spk _ _ _ _ _ he)
    | fst => exact Or.inr (hp (Or.inl rfl))
    | snd => exact Or.inr (hp (Or.inr rfl))
  | binary f a b =>
    cases f with
    | pair => exact False.elim (spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ _ he.symm)
    | partialDecrypt =>
      exact False.elim (spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ _ he.symm)
    | mul => exact False.elim (mul_not_eqE_spk _ _ _ _ _ _ he)
    | add => exact False.elim (arithmetic_not_eqE_spk .add (Or.inl rfl) _ _ _ _ _ _ he)
    | compose => exact False.elim (arithmetic_not_eqE_spk .compose (Or.inr rfl) _ _ _ _ _ _ he)
    | dec =>
      obtain ⟨out, hd, _⟩ := he.decryption_spk_inversion
      exact False.elim (minimum_decryption_no_match ns swap left right restricted a b hm out hd)
  | ternary f a b d =>
    cases f with
    | penc => exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ he)
    | checkspk => exact False.elim (proof_check_not_eqE_spk _ _ _ _ _ _ _ he)
  | spk a b c d => exact Or.inl ⟨a, b, c, d, rfl⟩

theorem key_projection_chain_not_spk (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) {recipe : Recipe 3} (h : ProjectionChain 0 recipe)
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
    (left right : Fin (n + 1)) (restricted : Finset Nat) (recipe : Recipe 3)
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

end ExplainableCrypto.Helios.Symbolic.Historical
