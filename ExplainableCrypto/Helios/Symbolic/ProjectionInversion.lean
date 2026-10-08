import ExplainableCrypto.Helios.Symbolic.ProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A pair-valued projection must actually reach and select from an argument pair. -/
theorem EqE.projection_pair_inversion {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a x y : Term V} (h : EqE (.unary f a) (.binary .pair x y)) :
    ∃ p q, ReducesModulo a (.binary .pair p q) ∧
      EqE (if f = .fst then p else q) (.binary .pair x y) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.projection_cases hf with ⟨_, _, ht⟩ | ⟨p, q, hp, hout⟩
  · obtain ⟨_, _, hpair, _⟩ := hr.passive_binary_components (Or.inl rfl)
    cases (ht.symm.trans hpair).head_eq
  · exact ⟨p, q, hp, hout.sound.trans hr.sound.symm⟩

theorem EqE.projection_spk_inversion {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a k r m c : Term V} (h : EqE (.unary f a) (.spk k r m c)) :
    ∃ p q, ReducesModulo a (.binary .pair p q) ∧
      EqE (if f = .fst then p else q) (.spk k r m c) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.projection_cases hf with ⟨_, _, ht⟩ | ⟨p, q, hp, hout⟩
  · obtain ⟨_, _, _, _, hproof, _⟩ := hr.spk_components
    cases (ht.symm.trans hproof).head_eq
  · exact ⟨p, q, hp, hout.sound.trans hr.sound.symm⟩

theorem pk_not_eqE_pair (k x y : Term V) :
    ¬ EqE (.unary .pk k) (.binary .pair x y) := by
  intro h
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨_, hk, _⟩ := hl.pk_components
  obtain ⟨_, _, hp, _⟩ := hr.passive_binary_components (Or.inl rfl)
  cases (hk.symm.trans hp).head_eq

end ExplainableCrypto.Helios.Symbolic
