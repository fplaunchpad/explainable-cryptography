import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem pk_path {s t : Term V} (h : ReducesModulo s t) {a : Term V}
    (he : BaseEq s (.unary .pk a)) :
    ∃ a', BaseEq t (.unary .pk a') ∧ ReducesModulo a a' := by
  induction h generalizing a with
  | base hb => exact ⟨a, hb.symm.trans he, .refl _⟩
  | head hs _ ih =>
    obtain ⟨a₁, ha, ht⟩ := (hs.pre_base he.symm).pk_cases
    obtain ⟨a₂, ht₂, ha₂⟩ := ih ht
    exact ⟨a₂, ht₂, (ReducesModulo.single ha).trans ha₂⟩

theorem ReducesModulo.pk_components {a t : Term V} (h : ReducesModulo (.unary .pk a) t) :
    ∃ a', BaseEq t (.unary .pk a') ∧ ReducesModulo a a' := pk_path h (.refl _)

theorem EqE.pk_iff (a b : Term V) : EqE (.unary .pk a) (.unary .pk b) ↔ EqE a b := by
  constructor
  · intro h
    obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
    obtain ⟨a', ht₁, ha⟩ := hl.pk_components
    obtain ⟨b', ht₂, hb⟩ := hr.pk_components
    have he := ((BaseEq.unary_iff _ _ _ _).mp (ht₁.symm.trans ht₂)).2
    exact ha.sound.trans (he.sound.trans hb.sound.symm)
  · exact EqE.unary .pk

theorem EqE.pk_irreducible_shape {a t : Term V} (h : EqE (.unary .pk a) t) (ht : Irreducible t) :
    ∃ a', t = .unary .pk a' ∧ EqE a a' := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨a₁, hw, ha⟩ := hl.pk_components
  obtain ⟨a₂, he, ha₂⟩ := ((ht.reducesModulo hr).trans hw).symm.unary_shape
  exact ⟨a₂, he, ha.sound.trans ha₂.sound⟩

theorem pk_not_eqE_penc (a k r m : Term V) : ¬ EqE (.unary .pk a) (.ternary .penc k r m) := by
  intro h
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨_, ht₁, _⟩ := hl.pk_components
  obtain ⟨_, _, _, ht₂, _⟩ := hr.penc_components
  have hh := (ht₁.symm.trans ht₂).head_eq
  cases hh

/-- A projection either remains at its head, or reaches a pair and selects a member.
The selector is metatheory; only fst/snd satisfy the public theorem's premise. -/
private theorem projection_path {f : Unary} (hf : f = .fst ∨ f = .snd)
    {s t : Term V} (h : ReducesModulo s t) {a : Term V} (he : BaseEq s (.unary f a)) :
    (∃ a', ReducesModulo a a' ∧ BaseEq t (.unary f a')) ∨
    (∃ x y, ReducesModulo a (.binary .pair x y) ∧ ReducesModulo (if f = .fst then x else y) t) := by
  induction h generalizing a with
  | base hb => exact Or.inl ⟨a, .refl _, hb.symm.trans he⟩
  | head hs hr ih =>
    rcases (hs.pre_base he.symm).unary_cases with hroot | ⟨a₁, ha, ht⟩
    · rcases hroot.unary_projection_cases with ⟨x, y, rfl, hp, hout⟩ | ⟨x, y, rfl, hp, hout⟩
      · exact Or.inr ⟨x, y, .base hp, by simpa using hr.pre_base hout⟩
      · exact Or.inr ⟨x, y, .base hp, by simpa using hr.pre_base hout⟩
    · rcases ih ht with ⟨a₂, ha₂, ht₂⟩ | ⟨x, y, hp, hout⟩
      · exact Or.inl ⟨a₂, (ReducesModulo.single ha).trans ha₂, ht₂⟩
      · exact Or.inr ⟨x, y, (ReducesModulo.single ha).trans hp, hout⟩

theorem ReducesModulo.projection_cases {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a t : Term V} (h : ReducesModulo (.unary f a) t) :
    (∃ a', ReducesModulo a a' ∧ BaseEq t (.unary f a')) ∨
    (∃ x y, ReducesModulo a (.binary .pair x y) ∧ ReducesModulo (if f = .fst then x else y) t) :=
  projection_path hf h (.refl _)

/-- A ciphertext result forces an actual pair-producing argument path. It does
not force the original argument to be a literal pair or a public-handle projection. -/
theorem EqE.projection_penc_inversion {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a k r m : Term V} (h : EqE (.unary f a) (.ternary .penc k r m)) :
    ∃ x y, ReducesModulo a (.binary .pair x y) ∧
      EqE (if f = .fst then x else y) (.ternary .penc k r m) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
  rcases hl.projection_cases hf with ⟨a', _, ht⟩ | ⟨x, y, hp, hout⟩
  · obtain ⟨_, _, _, hct, _⟩ := hr.penc_components
    have hh := (ht.symm.trans hct).head_eq
    cases hh
  · exact ⟨x, y, hp, hout.sound.trans hr.sound.symm⟩

end ExplainableCrypto.Helios.Symbolic
