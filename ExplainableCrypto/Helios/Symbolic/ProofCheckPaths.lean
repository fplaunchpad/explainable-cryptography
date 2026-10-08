import ExplainableCrypto.Helios.Symbolic.DecryptionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- All three arguments can reach one E8/E9 instance, including the bit guard
and the identical bound ciphertext. This is a relation on actual paths. -/
def ProofCheckMatch (a b c : Term V) : Prop :=
  ∃ k r bit, (bit = Constant.zero ∨ bit = .one) ∧
    ReducesModulo a k ∧ ReducesModulo b (bitCiphertext k r bit) ∧
    ReducesModulo c (bitProof k r bit)

theorem ProofCheckMatch.pre {a b c a' b' c' : Term V}
    (h : ProofCheckMatch a' b' c')
    (ha : ReducesModulo a a') (hb : ReducesModulo b b') (hc : ReducesModulo c c') :
    ProofCheckMatch a b c := by
  obtain ⟨k, r, bit, hbit, h₁, h₂, h₃⟩ := h
  exact ⟨k, r, bit, hbit, ha.trans h₁, hb.trans h₂, hc.trans h₃⟩

theorem ProofCheckMatch.reduces {a b c : Term V} (h : ProofCheckMatch a b c) :
    ReducesModulo (.ternary .checkspk a b c) (.const .ok) := by
  obtain ⟨k, r, bit, hbit, ha, hb, hc⟩ := h
  exact (ReducesModulo.ternary .checkspk ha hb hc).trans
    (.single (RootStep.check_bit k r bit hbit).to_modulo)

theorem BaseEq.ok_shape {t : Term V} (h : BaseEq (.const .ok) t) : t = .const .ok := by
  have hh := h.head_eq
  cases t with
  | const c => cases c <;> first | rfl | cases hh
  | binary f => cases f <;> cases hh
  | _ => cases hh

private theorem proof_check_path {s t : Term V} (h : ReducesModulo s t) {a b c : Term V}
    (he : BaseEq s (.ternary .checkspk a b c)) :
    (∃ a' b' c', ReducesModulo a a' ∧ ReducesModulo b b' ∧ ReducesModulo c c' ∧
      BaseEq t (.ternary .checkspk a' b' c')) ∨
    (ProofCheckMatch a b c ∧ t = .const .ok) := by
  induction h generalizing a b c with
  | base hb => exact Or.inl ⟨a, b, c, .refl _, .refl _, .refl _, hb.symm.trans he⟩
  | head hs hr ih =>
    rcases (hs.pre_base he.symm).ternary_cases with hroot | hargs
    · obtain ⟨k, r, bit, hbit, ha, hb, hc, hout⟩ := hroot.proof_check_cases
      exact Or.inr ⟨⟨k, r, bit, hbit, .base ha, .base hb, .base hc⟩,
        ((constant_irreducible .ok).reducesModulo (hr.pre_base hout)).ok_shape⟩
    · obtain ⟨a₁, b₁, c₁, ht, ha, hb, hc⟩ := hargs.components
      have ha₁ : ReducesModulo a a₁ := ha.elim ReducesModulo.base ReducesModulo.single
      have hb₁ : ReducesModulo b b₁ := hb.elim ReducesModulo.base ReducesModulo.single
      have hc₁ : ReducesModulo c c₁ := hc.elim ReducesModulo.base ReducesModulo.single
      rcases ih ht with ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, ht₂⟩ | ⟨hm, hout⟩
      · exact Or.inl ⟨a₂, b₂, c₂, ha₁.trans ha₂, hb₁.trans hb₂, hc₁.trans hc₂, ht₂⟩
      · exact Or.inr ⟨hm.pre ha₁ hb₁ hc₁, hout⟩

/-- Exhaustive actual path cases, including zero steps and arbitrary E0 endpoints. -/
theorem ReducesModulo.proof_check_cases {a b c t : Term V}
    (h : ReducesModulo (.ternary .checkspk a b c) t) :
    (∃ a' b' c', ReducesModulo a a' ∧ ReducesModulo b b' ∧ ReducesModulo c c' ∧
      BaseEq t (.ternary .checkspk a' b' c')) ∨
    (ProofCheckMatch a b c ∧ t = .const .ok) := proof_check_path h (.refl _)

/-- Successful checking under full E is exactly reachable E8/E9 argument matching. -/
theorem EqE.check_ok_iff (a b c : Term V) :
    EqE (.ternary .checkspk a b c) (.const .ok) ↔ ProofCheckMatch a b c := by
  constructor
  · intro h
    obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
    rcases hl.proof_check_cases with ⟨_, _, _, _, _, _, ht⟩ | ⟨hm, _⟩
    · have he := ((constant_irreducible .ok).reducesModulo hr).trans ht
      cases he.head_eq
    · exact hm
  · exact fun h => h.reduces.sound

/-- A successful check exposes one common nonce, a bit, and the complete
supplied ciphertext in the proof's binding field, all under full E. -/
theorem EqE.check_ok_iff_components (a b c : Term V) :
    EqE (.ternary .checkspk a b c) (.const .ok) ↔
      ∃ r bit, (bit = Constant.zero ∨ bit = .one) ∧
        EqE b (.ternary .penc a r (.const bit)) ∧ EqE c (.spk a r (.const bit) b) := by
  constructor
  · intro h
    obtain ⟨k, r, bit, hbit, ha, hb, hc⟩ := (EqE.check_ok_iff a b c).mp h
    exact ⟨r, bit, hbit,
      hb.sound.trans (.ternary .penc ha.sound.symm (.refl _) (.refl _)),
      hc.sound.trans (.spk ha.sound.symm (.refl _) (.refl _) hb.sound.symm)⟩
  · rintro ⟨r, bit, hbit, hb, hc⟩
    exact (EqE.ternary .checkspk (.refl _) hb
      (hc.trans (.spk (.refl _) (.refl _) (.refl _) hb))).trans
        (RootStep.check_bit a r bit hbit).sound

theorem ReducesModulo.proof_check_shape {a b c t : Term V}
    (h : ReducesModulo (.ternary .checkspk a b c) t) :
    (∃ a' b' c', t = .ternary .checkspk a' b' c') ∨ t = .const .ok := by
  rcases h.proof_check_cases with ⟨_, _, _, _, _, _, he⟩ | ⟨_, he⟩
  · obtain ⟨a', b', c', ht, _⟩ := he.symm.ternary_shape
    exact Or.inl ⟨a', b', c', ht⟩
  · exact Or.inr he

/-- Normal representatives preserve component E-values in the retained-head case. -/
theorem EqE.proof_check_irreducible_shape {a b c t : Term V}
    (h : EqE (.ternary .checkspk a b c) t) (ht : Irreducible t) :
    (∃ a' b' c', t = .ternary .checkspk a' b' c' ∧ EqE a a' ∧ EqE b b' ∧ EqE c c') ∨
    (ProofCheckMatch a b c ∧ t = .const .ok) := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.proof_check_cases with ⟨a₁, b₁, c₁, ha, hb, hc, hw⟩ | ⟨hm, rfl⟩
  · obtain ⟨a₂, b₂, c₂, he, ha₂, hb₂, hc₂⟩ :=
      ((ht.reducesModulo hr).trans hw).symm.ternary_shape
    exact Or.inl ⟨a₂, b₂, c₂, he, ha.sound.trans ha₂.sound,
      hb.sound.trans hb₂.sound, hc.sound.trans hc₂.sound⟩
  · exact Or.inr ⟨hm, (ht.reducesModulo hr).symm.ok_shape⟩

theorem proof_check_normal_shape_of_no_match (a b c : Term V) (hn : ¬ ProofCheckMatch a b c)
    {t : Term V} (ht : Irreducible t) (he : EqE (.ternary .checkspk a b c) t) :
    ∃ a' b' c', t = .ternary .checkspk a' b' c' ∧ EqE a a' ∧ EqE b b' ∧ EqE c c' := by
  rcases he.proof_check_irreducible_shape ht with hs | ⟨hm, _⟩
  · exact hs
  · exact False.elim (hn hm)

theorem proof_check_normal_form_of_no_match (a b c : Term V) (hn : ¬ ProofCheckMatch a b c)
    {a' b' c' t : Term V} (ha : Irreducible a') (hb : Irreducible b') (hc : Irreducible c')
    (ht : Irreducible t) (hea : EqE a a') (heb : EqE b b') (hec : EqE c c')
    (he : EqE (.ternary .checkspk a b c) t) : BaseEq t (.ternary .checkspk a' b' c') := by
  obtain ⟨a₁, b₁, c₁, rfl, h₁, h₂, h₃⟩ := proof_check_normal_shape_of_no_match a b c hn ht he
  have ha₁ := ht.context_hole (.ternaryFirst .checkspk .hole b₁ c₁)
  have hb₁ := ht.context_hole (.ternarySecond .checkspk a₁ .hole c₁)
  have hc₁ := ht.context_hole (.ternaryThird .checkspk a₁ b₁ .hole)
  exact .ternary .checkspk
    ((irreducible_eqE_iff_base ha₁ ha).mp (h₁.symm.trans hea))
    ((irreducible_eqE_iff_base hb₁ hb).mp (h₂.symm.trans heb))
    ((irreducible_eqE_iff_base hc₁ hc).mp (h₃.symm.trans hec))

end ExplainableCrypto.Helios.Symbolic
