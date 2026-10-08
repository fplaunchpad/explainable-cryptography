import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- E5 or E6 is reachable with the same key and complete ciphertext. This relation
records actual argument paths; it adds no public operation or equation. -/
def DecryptionMatch (a b m : Term V) : Prop :=
  ∃ k r, (ReducesModulo a k ∨
    ReducesModulo a (.binary .partialDecrypt k (keyCiphertext k r m))) ∧
    ReducesModulo b (keyCiphertext k r m)

namespace DecryptionMatch

theorem pre_left {a a' b m : Term V} (h : DecryptionMatch a' b m)
    (ha : ReducesModulo a a') : DecryptionMatch a b m := by
  obtain ⟨k, r, hk, hb⟩ := h
  exact ⟨k, r, hk.elim (fun h => Or.inl (ha.trans h))
    (fun h => Or.inr (ha.trans h)), hb⟩

theorem pre_right {a b b' m : Term V} (h : DecryptionMatch a b' m)
    (hb : ReducesModulo b b') : DecryptionMatch a b m := by
  obtain ⟨k, r, hk, hc⟩ := h
  exact ⟨k, r, hk, hb.trans hc⟩

theorem reduces {a b m : Term V} (h : DecryptionMatch a b m) :
    ReducesModulo (.binary .dec a b) m := by
  obtain ⟨k, r, hk, hc⟩ := h
  rcases hk with hk | hk
  · exact (ReducesModulo.binary .dec hk hc).trans (.single (RootStep.decrypt k r m).to_modulo)
  · exact (ReducesModulo.binary .dec hk hc).trans (.single (RootStep.partial_decrypt k r m).to_modulo)

end DecryptionMatch

private theorem decryption_path {s t : Term V} (h : ReducesModulo s t) {a b : Term V}
    (he : BaseEq s (.binary .dec a b)) :
    (∃ a' b', ReducesModulo a a' ∧ ReducesModulo b b' ∧ BaseEq t (.binary .dec a' b')) ∨
    (∃ m, DecryptionMatch a b m ∧ ReducesModulo m t) := by
  induction h generalizing a b with
  | base hb => exact Or.inl ⟨a, b, .refl _, .refl _, hb.symm.trans he⟩
  | head hs hr ih =>
    rcases (hs.pre_base he.symm).rigid_binary_cases (by simp [AC]) with
      hroot | ⟨a₁, ha, ht⟩ | ⟨b₁, hb, ht⟩
    · rcases hroot.decryption_cases with ⟨k, r, m, ha, hb, hm⟩ | ⟨k, r, m, ha, hb, hm⟩
      · exact Or.inr ⟨m, ⟨k, r, Or.inl (.base ha), .base hb⟩, hr.pre_base hm⟩
      · exact Or.inr ⟨m, ⟨k, r, Or.inr (.base ha), .base hb⟩, hr.pre_base hm⟩
    · rcases ih ht with ⟨a₂, b₂, ha₂, hb₂, ht₂⟩ | ⟨m, hmatch, hm⟩
      · exact Or.inl ⟨a₂, b₂, (ReducesModulo.single ha).trans ha₂, hb₂, ht₂⟩
      · exact Or.inr ⟨m, hmatch.pre_left (.single ha), hm⟩
    · rcases ih ht with ⟨a₂, b₂, ha₂, hb₂, ht₂⟩ | ⟨m, hmatch, hm⟩
      · exact Or.inl ⟨a₂, b₂, ha₂, (ReducesModulo.single hb).trans hb₂, ht₂⟩
      · exact Or.inr ⟨m, hmatch.pre_right (.single hb), hm⟩

/-- Exhaustive path cases, including arbitrary E0 representatives and a zero-step path.
The alternatives need not be disjoint when returned plaintext itself has a dec head. -/
theorem ReducesModulo.decryption_cases {a b t : Term V}
    (h : ReducesModulo (.binary .dec a b) t) :
    (∃ a' b', ReducesModulo a a' ∧ ReducesModulo b b' ∧ BaseEq t (.binary .dec a' b')) ∨
    (∃ m, DecryptionMatch a b m ∧ ReducesModulo m t) := decryption_path h (.refl _)

/-- A ciphertext-valued decrypt must have reached E5 or E6; its original arguments
need not have the matching literal shapes. Target components can be reducible. -/
theorem EqE.decryption_penc_inversion {a b k r m : Term V}
    (h : EqE (.binary .dec a b) (.ternary .penc k r m)) :
    ∃ p, DecryptionMatch a b p ∧ EqE p (.ternary .penc k r m) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.decryption_cases with ⟨_, _, _, _, ht⟩ | ⟨p, hp, hout⟩
  · obtain ⟨_, _, _, hc, _⟩ := hr.penc_components
    cases (ht.symm.trans hc).head_eq
  · exact ⟨p, hp, hout.sound.trans hr.sound.symm⟩

/-- If no argument match is reachable, every irreducible E-value retains dec. -/
theorem decryption_normal_shape_of_no_match (a b : Term V)
    (hn : ∀ m, ¬ DecryptionMatch a b m) {t : Term V}
    (ht : Irreducible t) (he : EqE (.binary .dec a b) t) :
    ∃ a' b', t = .binary .dec a' b' ∧ EqE a a' ∧ EqE b b' := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.decryption_cases with ⟨a₁, b₁, ha, hb, hw⟩ | ⟨m, hm, _⟩
  · obtain ⟨a₂, b₂, ht₂, ha₂, hb₂⟩ :=
      ((ht.reducesModulo hr).trans hw).symm.rigid_binary_shape (by simp [AC])
    exact ⟨a₂, b₂, ht₂, ha.sound.trans ha₂.sound, hb.sound.trans hb₂.sound⟩
  · exact False.elim (hn m hm)

/-- Every one-hole subterm of an irreducible term is irreducible. -/
theorem Irreducible.context_hole (c : Context V) {a : Term V}
    (h : Irreducible (c.fill a)) : Irreducible a :=
  fun b hb => h (c.fill b) (hb.context c)

/-- Normalizing the arguments separately agrees modulo E0 with normalizing the
whole decrypt, provided no E5/E6 argument match is reachable. -/
theorem decryption_normal_form_of_no_match (a b : Term V)
    (hn : ∀ m, ¬ DecryptionMatch a b m) {a' b' t : Term V}
    (ha : Irreducible a') (hb : Irreducible b') (ht : Irreducible t)
    (hea : EqE a a') (heb : EqE b b') (he : EqE (.binary .dec a b) t) :
    BaseEq t (.binary .dec a' b') := by
  obtain ⟨a₁, b₁, rfl, h₁, h₂⟩ := decryption_normal_shape_of_no_match a b hn ht he
  have ha₁ := ht.context_hole (.binaryLeft .dec .hole b₁)
  have hb₁ := ht.context_hole (.binaryRight .dec a₁ .hole)
  exact .binary .dec
    ((irreducible_eqE_iff_base ha₁ ha).mp (h₁.symm.trans hea))
    ((irreducible_eqE_iff_base hb₁ hb).mp (h₂.symm.trans heb))

/-- Matching an explicit ciphertext identifies the returned plaintext up to E. -/
theorem DecryptionMatch.explicit_plaintext {a key nonce p m : Term V}
    (h : DecryptionMatch a (.ternary .penc key nonce p) m) : EqE p m := by
  obtain ⟨k, r, _, hc⟩ := h
  exact ((EqE.penc_iff _ _ _ _ _ _).mp hc.sound).2.2

end ExplainableCrypto.Helios.Symbolic
