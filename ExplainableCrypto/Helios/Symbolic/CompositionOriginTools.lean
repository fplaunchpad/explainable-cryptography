import ExplainableCrypto.Helios.Symbolic.FullCompositionFactors

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {policy : Finset Nat} {handles : Nat}

/-- Composition syntax follows from handle exclusions and actual projection/
decryption output paths. Decryption may succeed with a non-composition output;
no minimum or cross-frame assumption is hidden in this structural helper. -/
theorem compose_form_of_paths (ψ : Frame policy handles) (r : Recipe handles)
    (hhandles : ∀ v x y, ¬ EqE (ψ.value v) (.binary .compose x y))
    (hd : ∀ a b, r = .binary .dec a b → ∀ out, DecryptionMatch (ψ.eval a) (ψ.eval b) out →
      ∀ x y, ¬ EqE out (.binary .compose x y))
    (hp : ∀ f a, r = .unary f a → (f = .fst ∨ f = .snd) → (ψ.eval a).PairValue →
      (∃ x y, EqE (ψ.eval r) (.binary .pair x y)) ∨
      (∃ k s m, EqE (ψ.eval r) (.ternary .penc k s m)) ∨
      (∃ k s m c, EqE (ψ.eval r) (.spk k s m c)))
    {x y : Ground} (he : EqE (ψ.eval r) (.binary .compose x y)) :
    ∃ a b, r = .binary .compose a b := by
  obtain ⟨t, hpath, ht⟩ := exists_normal_form (.binary .compose x y)
  obtain ⟨x', y', rfl⟩ := hpath.to_modulo.sound.compose_irreducible_shape ht
  have he := he.trans hpath.to_modulo.sound
  have notPair {a b : Ground} (hv : EqE (ψ.eval r) (.binary .pair a b)) : False :=
    arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _ (he.symm.trans hv)
  cases r with
  | name a => exact False.elim (arithmetic_not_eqE_name .compose (Or.inr rfl) _ _ a he.symm)
  | const c =>
    have h := he.symm.arithmetic_constant_cases (Or.inr rfl)
    cases h.1
  | var v => exact False.elim (hhandles v _ _ he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.projection_cases hf with ⟨_, _, hw⟩ | ⟨u, v, huv, _⟩
      · cases ((ht.reducesModulo hr).trans hw).head_eq
      · rcases hp f a rfl hf ⟨u,v,huv.sound⟩ with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, hv⟩
        · exact notPair hv
        · exact arithmetic_not_eqE_penc .compose (Or.inr rfl) _ _ _ _ _ (he.symm.trans hv)
        · exact arithmetic_not_eqE_spk .compose (Or.inr rfl) _ _ _ _ _ _ (he.symm.trans hv)
    cases f with
    | pk => exact False.elim (arithmetic_not_eqE_pk .compose (Or.inr rfl) _ _ _ he.symm)
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | compose => exact ⟨a, b, rfl⟩
    | pair => exact False.elim (notPair (.refl _))
    | partialDecrypt =>
      exact False.elim (arithmetic_not_eqE_passive_binary .compose .partialDecrypt (Or.inr rfl) (Or.inr rfl) _ _ _ _ he.symm)
    | add => exact False.elim (compose_not_eqE_add _ _ _ _ he.symm)
    | mul => exact False.elim (arithmetic_not_eqE_mul .compose (Or.inr rfl) _ _ _ _ he.symm)
    | dec =>
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.decryption_cases with ⟨_, _, _, _, hw⟩ | ⟨m, hm, hout⟩
      · cases ((ht.reducesModulo hr).trans hw).head_eq
      · exact False.elim (hd a b rfl m hm _ _ (hout.sound.trans hr.sound.symm))
  | ternary f a b c =>
    cases f with
    | penc => exact False.elim (arithmetic_not_eqE_penc .compose (Or.inr rfl) _ _ _ _ _ he.symm)
    | checkspk =>
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.proof_check_cases with ⟨_, _, _, _, _, _, hw⟩ | ⟨_, rfl⟩
      · cases ((ht.reducesModulo hr).trans hw).head_eq
      · cases (ht.reducesModulo hr).head_eq
  | spk a b c d => exact False.elim (arithmetic_not_eqE_spk .compose (Or.inr rfl) _ _ _ _ _ _ he.symm)

end ExplainableCrypto.Helios.Symbolic.Frame
