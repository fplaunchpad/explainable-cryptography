import ExplainableCrypto.Helios.Symbolic.MinimumProjectionObservations

namespace ExplainableCrypto.Helios.Symbolic
variable {policy : Finset Nat} {handles : Nat}

/-- A normal stuck-check value forces check syntax when handles and successful
minimum projections cannot supply it and whole minimum decryptions do not match. -/
theorem Frame.minimum_normal_check_form_of_origins (φ : Frame policy handles)
    (restricted : Finset Nat)
    (hproject : ∀ f : Unary, f = .fst ∨ f = .snd → ∀ a : Recipe handles,
      MinimalRecipe restricted φ.value (.unary f a) → ∀ x y,
      EqE (φ.eval a) (.binary .pair x y) →
      (∃ x y, EqE (φ.eval (.unary f a)) (.binary .pair x y)) ∨
      (∃ k r m, EqE (φ.eval (.unary f a)) (.ternary .penc k r m)) ∨
      (∃ k r m c, EqE (φ.eval (.unary f a)) (.spk k r m c)))
    (hdec : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .dec a b) →
      ∀ out, ¬ DecryptionMatch (φ.eval a) (φ.eval b) out)
    (r : Recipe handles) (hm : MinimalRecipe restricted φ.value r) {k c p : Ground}
    (ht : Irreducible (.ternary .checkspk k c p))
    (hhandles : ∀ v, ¬ EqE (φ.value v) (.ternary .checkspk k c p))
    (he : EqE (φ.eval r) (.ternary .checkspk k c p)) :
    ∃ a b d, r = .ternary .checkspk a b d := by
  have notPair {a b : Ground} (hv : EqE (φ.eval r) (.binary .pair a b)) : False :=
    proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ (he.symm.trans hv)
  cases r with
  | name name => exact False.elim (proof_check_not_eqE_name _ _ _ name he.symm)
  | const d =>
    have hh := ((irreducible_eqE_iff_base (constant_irreducible d) ht).mp he).head_eq
    cases d <;> cases hh
  | var v => exact False.elim (hhandles v he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.projection_cases hf with ⟨a', _, hw⟩ | ⟨x, y, hp, _⟩
      · have hh := ((ht.reducesModulo hr).trans hw).head_eq
        cases hh
      · rcases hproject f hf a hm x y hp.sound with ⟨x, y, hv⟩ | ⟨k', r', m', hv⟩ | ⟨k', r', m', c', hv⟩
        · exact notPair hv
        · exact proof_check_not_eqE_penc _ _ _ _ _ _ (he.symm.trans hv)
        · exact proof_check_not_eqE_spk _ _ _ _ _ _ _ (he.symm.trans hv)
    cases f with
    | pk => exact False.elim (proof_check_not_eqE_pk _ _ _ _ he.symm)
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | pair => exact False.elim (proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ he.symm)
    | partialDecrypt =>
      exact False.elim
        (proof_check_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he.symm)
    | mul =>
      rcases he.mul_irreducible_shape ht with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
    | add =>
      rcases he.add_irreducible_shape ht with ⟨_, _, h⟩ | h | h <;> cases h
    | compose =>
      obtain ⟨_, _, h⟩ := he.compose_irreducible_shape ht
      cases h
    | dec =>
      obtain ⟨_, _, h, _⟩ := decryption_normal_shape_of_no_match _ _
        (hdec a b hm) ht he
      cases h
  | ternary f a b d =>
    cases f with
    | penc => exact False.elim (proof_check_not_eqE_penc _ _ _ _ _ _ he.symm)
    | checkspk => exact ⟨a, b, d, rfl⟩
  | spk a b d e => exact False.elim (proof_check_not_eqE_spk _ _ _ _ _ _ _ he.symm)

end ExplainableCrypto.Helios.Symbolic
