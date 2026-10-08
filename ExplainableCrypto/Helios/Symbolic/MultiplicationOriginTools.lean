import ExplainableCrypto.Helios.Symbolic.AdditionObservationInduction

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {policy : Finset Nat} {handles : Nat}

/-- Exact normal-product syntax follows from frame-specific handle and actual
output exclusions. Successful decryption is allowed when its output cannot be
a normal product; no hidden minimum or cross-frame premise is used. -/
theorem normal_mul_form_of_paths (ψ : Frame policy handles) (r : Recipe handles)
    (hhandles : ∀ v x y, Irreducible (.binary .mul x y) → ¬ EqE (ψ.value v) (.binary .mul x y))
    (hd : ∀ a b, r = .binary .dec a b → ∀ out, DecryptionMatch (ψ.eval a) (ψ.eval b) out →
      ∀ x y, Irreducible (.binary .mul x y) → ¬ EqE out (.binary .mul x y))
    (hp : ∀ f a, r = .unary f a → (f = .fst ∨ f = .snd) → (ψ.eval a).PairValue →
      (∃ x y, EqE (ψ.eval r) (.binary .pair x y)) ∨
      (∃ k s m, EqE (ψ.eval r) (.ternary .penc k s m)) ∨
      (∃ k s m c, EqE (ψ.eval r) (.spk k s m c)))
    {x y : Ground} (ht : Irreducible (.binary .mul x y))
    (he : EqE (ψ.eval r) (.binary .mul x y)) : ∃ a b, r = .binary .mul a b := by
  have notPair {a b : Ground} (hv : EqE (ψ.eval r) (.binary .pair a b)) : False :=
    mul_not_eqE_passive_binary _ _ _ _ .pair (Or.inl rfl) (he.symm.trans hv)
  have notPenc {k r' m : Ground} (hv : EqE (ψ.eval r) (.ternary .penc k r' m)) : False := by
    obtain ⟨_, _, _, bad, _⟩ := (hv.symm.trans he).penc_irreducible_shape ht
    cases bad
  cases r with
  | name a => exact False.elim (mul_not_eqE_name _ _ a he.symm)
  | const c => exact False.elim (mul_not_eqE_constant _ _ c he.symm)
  | var v => exact False.elim (hhandles v _ _ ht he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.projection_cases hf with ⟨_, _, hw⟩ | ⟨u, v, huv, _⟩
      · cases ((ht.reducesModulo hr).trans hw).head_eq
      · rcases hp f a rfl hf ⟨u,v,huv.sound⟩ with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, hv⟩
        · exact notPair hv
        · exact notPenc hv
        · exact mul_not_eqE_spk _ _ _ _ _ _ (he.symm.trans hv)
    cases f with
    | pk => exact False.elim (mul_not_eqE_pk _ _ _ he.symm)
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | mul => exact ⟨a, b, rfl⟩
    | pair => exact False.elim (notPair (.refl _))
    | partialDecrypt =>
      exact False.elim (mul_not_eqE_passive_binary _ _ _ _ .partialDecrypt (Or.inr rfl) he.symm)
    | add => exact False.elim (arithmetic_not_eqE_mul .add (Or.inl rfl) _ _ _ _ he)
    | compose => exact False.elim (arithmetic_not_eqE_mul .compose (Or.inr rfl) _ _ _ _ he)
    | dec =>
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.decryption_cases with ⟨_, _, _, _, hw⟩ | ⟨m, hm, hout⟩
      · cases ((ht.reducesModulo hr).trans hw).head_eq
      · exact False.elim (hd a b rfl m hm _ _ ht (hout.sound.trans hr.sound.symm))
  | ternary f a b c =>
    cases f with
    | penc => exact False.elim (notPenc (.refl _))
    | checkspk =>
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.proof_check_cases with ⟨_, _, _, _, _, _, hw⟩ | ⟨_, rfl⟩
      · cases ((ht.reducesModulo hr).trans hw).head_eq
      · cases (ht.reducesModulo hr).head_eq
  | spk a b c d => exact False.elim (mul_not_eqE_spk _ _ _ _ _ _ he.symm)

end ExplainableCrypto.Helios.Symbolic.Frame
