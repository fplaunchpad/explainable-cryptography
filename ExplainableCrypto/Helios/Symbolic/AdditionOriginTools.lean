import ExplainableCrypto.Helios.Symbolic.FullAdditionSummary

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {policy : Finset Nat} {handles : Nat}

/-- Addition origins permit a frame-specific class of additive handles.
Successful projections supply data; the explicit decryption premise concerns
actual matching, not failed raw normalization. -/
theorem add_form_of_paths (ψ : Frame policy handles) (r : Recipe handles) (extra : Recipe handles → Prop)
    (hhandles : ∀ v x y, EqE (ψ.value v) (.binary .add x y) → extra (.var v))
    (hd : ∀ a b, r = .binary .dec a b → ∀ out, ¬ DecryptionMatch (ψ.eval a) (ψ.eval b) out)
    (hp : ∀ f a, r = .unary f a → (f = .fst ∨ f = .snd) → (ψ.eval a).PairValue →
      (∃ x y, EqE (ψ.eval r) (.binary .pair x y)) ∨
      (∃ k s m, EqE (ψ.eval r) (.ternary .penc k s m)) ∨
      (∃ k s m c, EqE (ψ.eval r) (.spk k s m c)))
    {x y : Ground} (he : EqE (ψ.eval r) (.binary .add x y)) :
    ((∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one) ∨ extra r := by
  obtain ⟨t, hpath, ht⟩ := exists_normal_form (.binary .add x y)
  have hh := hpath.to_modulo.sound.arithmetic_irreducible_head_tag (Or.inl rfl) ht
  have hen := he.trans hpath.to_modulo.sound
  have notPair {a b : Ground} (hv : EqE (ψ.eval r) (.binary .pair a b)) : False :=
    arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ _ _ (he.symm.trans hv)
  cases r with
  | name a => exact False.elim (arithmetic_not_eqE_name .add (Or.inl rfl) _ _ a he.symm)
  | const c =>
    have h := he.symm.arithmetic_constant_cases (Or.inl rfl)
    rcases h.2 with rfl | rfl
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr rfl))
  | var v => exact Or.inr (hhandles v _ _ he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp hen
      rcases hl.projection_cases hf with ⟨_, _, hw⟩ | ⟨u, v, huv, _⟩
      · have bad := ((ht.reducesModulo hr).trans hw).head_eq
        rw [hh] at bad
        cases bad
      · rcases hp f a rfl hf ⟨u,v,huv.sound⟩ with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, hv⟩
        · exact notPair hv
        · exact arithmetic_not_eqE_penc .add (Or.inl rfl) _ _ _ _ _ (he.symm.trans hv)
        · exact arithmetic_not_eqE_spk .add (Or.inl rfl) _ _ _ _ _ _ (he.symm.trans hv)
    cases f with
    | pk => exact False.elim (arithmetic_not_eqE_pk .add (Or.inl rfl) _ _ _ he.symm)
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | add => exact Or.inl (Or.inl ⟨a, b, rfl⟩)
    | pair => exact False.elim (notPair (.refl _))
    | partialDecrypt =>
      exact False.elim (arithmetic_not_eqE_passive_binary .add .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _ he.symm)
    | compose => exact False.elim (compose_not_eqE_add _ _ _ _ he)
    | mul => exact False.elim (arithmetic_not_eqE_mul .add (Or.inl rfl) _ _ _ _ he.symm)
    | dec =>
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp hen
      rcases hl.decryption_cases with ⟨_, _, _, _, hw⟩ | ⟨m, hm, _⟩
      · have bad := ((ht.reducesModulo hr).trans hw).head_eq
        rw [hh] at bad
        cases bad
      · exact False.elim (hd a b rfl m hm)
  | ternary f a b c =>
    cases f with
    | penc => exact False.elim (arithmetic_not_eqE_penc .add (Or.inl rfl) _ _ _ _ _ he.symm)
    | checkspk =>
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp hen
      rcases hl.proof_check_cases with ⟨_, _, _, _, _, _, hw⟩ | ⟨_, rfl⟩
      · have bad := ((ht.reducesModulo hr).trans hw).head_eq
        rw [hh] at bad
        cases bad
      · have bad := (ht.reducesModulo hr).head_eq
        rw [hh] at bad
        cases bad
  | spk a b c d => exact False.elim (arithmetic_not_eqE_spk .add (Or.inl rfl) _ _ _ _ _ _ he.symm)

end ExplainableCrypto.Helios.Symbolic.Frame
