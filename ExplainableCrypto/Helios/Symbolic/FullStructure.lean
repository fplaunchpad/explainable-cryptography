import ExplainableCrypto.Helios.Symbolic.PassiveReduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem component_equality {a a' b b' : Term V}
    (ha : ReducesModulo a a') (hb : ReducesModulo b b') (he : BaseEq a' b') : EqE a b :=
  ha.sound.trans (he.sound.trans hb.sound.symm)

/-- Full-E ciphertext injectivity holds for arbitrary, possibly reducible inputs. -/
theorem EqE.penc_iff (k r m k' r' m' : Term V) :
    EqE (.ternary .penc k r m) (.ternary .penc k' r' m') ↔
      EqE k k' ∧ EqE r r' ∧ EqE m m' := by
  constructor
  · intro h
    obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
    obtain ⟨k₁, r₁, m₁, ht₁, hk₁, hr₁, hm₁⟩ := hl.penc_components
    obtain ⟨k₂, r₂, m₂, ht₂, hk₂, hr₂, hm₂⟩ := hr.penc_components
    obtain ⟨hk, hr, hm⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp (ht₁.symm.trans ht₂)
    exact ⟨component_equality hk₁ hk₂ hk, component_equality hr₁ hr₂ hr, component_equality hm₁ hm₂ hm⟩
  · rintro ⟨hk, hr, hm⟩
    exact .ternary .penc hk hr hm

theorem EqE.spk_iff (a b c d a' b' c' d' : Term V) :
    EqE (.spk a b c d) (.spk a' b' c' d') ↔
      EqE a a' ∧ EqE b b' ∧ EqE c c' ∧ EqE d d' := by
  constructor
  · intro h
    obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
    obtain ⟨a₁, b₁, c₁, d₁, ht₁, ha₁, hb₁, hc₁, hd₁⟩ := hl.spk_components
    obtain ⟨a₂, b₂, c₂, d₂, ht₂, ha₂, hb₂, hc₂, hd₂⟩ := hr.spk_components
    obtain ⟨ha, hb, hc, hd⟩ := (BaseEq.spk_iff _ _ _ _ _ _ _ _).mp (ht₁.symm.trans ht₂)
    exact ⟨component_equality ha₁ ha₂ ha, component_equality hb₁ hb₂ hb,
      component_equality hc₁ hc₂ hc, component_equality hd₁ hd₂ hd⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact .spk ha hb hc hd

theorem EqE.passive_binary_iff (f g : Binary)
    (hf : f = .pair ∨ f = .partialDecrypt) (hg : g = .pair ∨ g = .partialDecrypt)
    (a b a' b' : Term V) :
    EqE (.binary f a b) (.binary g a' b') ↔ f = g ∧ EqE a a' ∧ EqE b b' := by
  constructor
  · intro h
    obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
    obtain ⟨a₁, b₁, ht₁, ha₁, hb₁⟩ := hl.passive_binary_components hf
    obtain ⟨a₂, b₂, ht₂, ha₂, hb₂⟩ := hr.passive_binary_components hg
    have hfn : ¬ AC f := by rcases hf with rfl | rfl <;> simp [AC]
    have hgn : ¬ AC g := by rcases hg with rfl | rfl <;> simp [AC]
    obtain ⟨hfg, ha, hb⟩ := (BaseEq.binary_iff f g hfn hgn _ _ _ _).mp (ht₁.symm.trans ht₂)
    exact ⟨hfg, component_equality ha₁ ha₂ ha, component_equality hb₁ hb₂ hb⟩
  · rintro ⟨rfl, ha, hb⟩
    exact .binary f ha hb

theorem EqE.pair_iff (a b a' b' : Term V) :
    EqE (.binary .pair a b) (.binary .pair a' b') ↔ EqE a a' ∧ EqE b b' := by
  simpa using EqE.passive_binary_iff .pair .pair (Or.inl rfl) (Or.inl rfl) a b a' b'

theorem EqE.partialDecrypt_iff (a b a' b' : Term V) :
    EqE (.binary .partialDecrypt a b) (.binary .partialDecrypt a' b') ↔ EqE a a' ∧ EqE b b' := by
  simpa using EqE.passive_binary_iff .partialDecrypt .partialDecrypt (Or.inr rfl) (Or.inr rfl) a b a' b'

theorem penc_not_eqE_spk (k r m a b c d : Term V) :
    ¬ EqE (.ternary .penc k r m) (.spk a b c d) := by
  intro h
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨_, _, _, ht₁, _⟩ := hl.penc_components
  obtain ⟨_, _, _, _, ht₂, _⟩ := hr.spk_components
  exact penc_not_base_spk _ _ _ _ _ _ _ (ht₁.symm.trans ht₂)

theorem penc_not_eqE_passive_binary (f : Binary) (hf : f = .pair ∨ f = .partialDecrypt)
    (k r m a b : Term V) : ¬ EqE (.ternary .penc k r m) (.binary f a b) := by
  intro h
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨_, _, _, ht₁, _⟩ := hl.penc_components
  obtain ⟨_, _, ht₂, _⟩ := hr.passive_binary_components hf
  have hh := (ht₁.symm.trans ht₂).head_eq
  rcases hf with rfl | rfl <;> cases hh

theorem spk_not_eqE_passive_binary (f : Binary) (hf : f = .pair ∨ f = .partialDecrypt)
    (a b c d x y : Term V) : ¬ EqE (.spk a b c d) (.binary f x y) := by
  intro h
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨_, _, _, _, ht₁, _⟩ := hl.spk_components
  obtain ⟨_, _, ht₂, _⟩ := hr.passive_binary_components hf
  have hh := (ht₁.symm.trans ht₂).head_eq
  rcases hf with rfl | rfl <;> cases hh

theorem EqE.name_iff (n m : Nat) : EqE (Term.name (V := V) n) (.name m) ↔ n = m :=
  (irreducible_eqE_iff_base (name_irreducible n) (name_irreducible m)).trans (BaseEq.name_iff n m)

/-- A normal representative E-equal to a ciphertext has literal ciphertext shape.
The irreducibility premise excludes active destructors returning ciphertexts. -/
theorem EqE.penc_irreducible_shape {k r m t : Term V}
    (h : EqE (.ternary .penc k r m) t) (ht : Irreducible t) :
    ∃ k' r' m', t = .ternary .penc k' r' m' ∧ EqE k k' ∧ EqE r r' ∧ EqE m m' := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨k₁, r₁, m₁, hw, hk, hr₁, hm⟩ := hl.penc_components
  obtain ⟨k₂, r₂, m₂, he, hk₂, hr₂, hm₂⟩ :=
    ((ht.reducesModulo hr).trans hw).symm.penc_shape
  exact ⟨k₂, r₂, m₂, he, hk.sound.trans hk₂.sound,
    hr₁.sound.trans hr₂.sound, hm.sound.trans hm₂.sound⟩

theorem EqE.spk_irreducible_shape {a b c d t : Term V}
    (h : EqE (.spk a b c d) t) (ht : Irreducible t) :
    ∃ a' b' c' d', t = .spk a' b' c' d' ∧
      EqE a a' ∧ EqE b b' ∧ EqE c c' ∧ EqE d d' := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨a₁, b₁, c₁, d₁, hw, ha, hb, hc, hd⟩ := hl.spk_components
  obtain ⟨a₂, b₂, c₂, d₂, he, ha₂, hb₂, hc₂, hd₂⟩ :=
    ((ht.reducesModulo hr).trans hw).symm.spk_shape
  exact ⟨a₂, b₂, c₂, d₂, he, ha.sound.trans ha₂.sound,
    hb.sound.trans hb₂.sound, hc.sound.trans hc₂.sound, hd.sound.trans hd₂.sound⟩

end ExplainableCrypto.Helios.Symbolic
