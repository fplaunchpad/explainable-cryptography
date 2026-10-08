import ExplainableCrypto.Helios.Symbolic.DecryptionLocalConfluence
import ExplainableCrypto.Helios.Symbolic.AtomIrreducibility

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem BaseEq.spk_shape {a b c d t : Term V} (h : BaseEq (.spk a b c d) t) :
    ∃ a' b' c' d', t = .spk a' b' c' d' ∧
      BaseEq a a' ∧ BaseEq b b' ∧ BaseEq c c' ∧ BaseEq d d' := by
  have hh := h.head_eq
  cases t with
  | name => cases hh
  | var => cases hh
  | const e => cases e <;> cases hh
  | unary => cases hh
  | binary f => cases f <;> cases hh
  | ternary => cases hh
  | spk a' b' c' d' => exact ⟨a', b', c', d', rfl, (BaseEq.spk_iff _ _ _ _ _ _ _ _).mp h⟩

/-- Proof construction has no root rule; all four argument positions are covered. -/
theorem RewriteStep.spk_cases {a b c d t : Term V} (h : RewriteStep (.spk a b c d) t) :
    (∃ a', RewriteStep a a' ∧ t = .spk a' b c d) ∨
    (∃ b', RewriteStep b b' ∧ t = .spk a b' c d) ∨
    (∃ c', RewriteStep c c' ∧ t = .spk a b c' d) ∨
    (∃ d', RewriteStep d d' ∧ t = .spk a b c d') := by
  obtain ⟨ctx, l, r, hr, hs, rfl⟩ := h
  cases ctx with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    cases hr
  | spkFirst ctx x y z =>
    simp only [Context.fill, Term.spk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inl ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩
  | spkSecond x ctx y z =>
    simp only [Context.fill, Term.spk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inl ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩)
  | spkThird x y ctx z =>
    simp only [Context.fill, Term.spk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inr (Or.inl ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩))
  | spkFourth x y z ctx =>
    simp only [Context.fill, Term.spk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inr (Or.inr ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩))
  | _ => cases hs

/-- E0 changes in untouched proof components are absorbed by the target equality. -/
theorem ModuloStep.spk_cases {a b c d t : Term V} (h : ModuloStep (.spk a b c d) t) :
    (∃ a', ModuloStep a a' ∧ BaseEq t (.spk a' b c d)) ∨
    (∃ b', ModuloStep b b' ∧ BaseEq t (.spk a b' c d)) ∨
    (∃ c', ModuloStep c c' ∧ BaseEq t (.spk a b c' d)) ∨
    (∃ d', ModuloStep d d' ∧ BaseEq t (.spk a b c d')) := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  obtain ⟨a₀, b₀, c₀, d₀, rfl, ha, hb, hc, hd⟩ := hx.spk_shape
  rcases hxy.spk_cases with ⟨a', hs, rfl⟩ | ⟨b', hs, rfl⟩ | ⟨c', hs, rfl⟩ | ⟨d', hs, rfl⟩
  · exact Or.inl ⟨a', ⟨a₀, a', ha, hs, .refl _⟩,
      hy.symm.trans (.spk (.refl _) hb.symm hc.symm hd.symm)⟩
  · exact Or.inr (Or.inl ⟨b', ⟨b₀, b', hb, hs, .refl _⟩,
      hy.symm.trans (.spk ha.symm (.refl _) hc.symm hd.symm)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c', ⟨c₀, c', hc, hs, .refl _⟩,
      hy.symm.trans (.spk ha.symm hb.symm (.refl _) hd.symm)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d', ⟨d₀, d', hd, hs, .refl _⟩,
      hy.symm.trans (.spk ha.symm hb.symm hc.symm (.refl _))⟩))

theorem JoinModulo.spk {a a' b b' c c' d d' : Term V}
    (ha : JoinModulo a a') (hb : JoinModulo b b') (hc : JoinModulo c c') (hd : JoinModulo d d') :
    JoinModulo (.spk a b c d) (.spk a' b' c' d') := by
  obtain ⟨x, hx, hx'⟩ := ha
  obtain ⟨y, hy, hy'⟩ := hb
  obtain ⟨z, hz, hz'⟩ := hc
  obtain ⟨w, hw, hw'⟩ := hd
  exact ⟨.spk x y z w, .spk hx hy hz hw, .spk hx' hy' hz' hw'⟩

theorem ModuloStep.spk_components {a b c d t : Term V} (h : ModuloStep (.spk a b c d) t) :
    ∃ a' b' c' d', BaseEq t (.spk a' b' c' d') ∧
      (BaseEq a a' ∨ ModuloStep a a') ∧ (BaseEq b b' ∨ ModuloStep b b') ∧
      (BaseEq c c' ∨ ModuloStep c c') ∧ (BaseEq d d' ∨ ModuloStep d d') := by
  rcases h.spk_cases with ⟨a', ha, he⟩ | ⟨b', hb, he⟩ | ⟨c', hc, he⟩ | ⟨d', hd, he⟩
  · exact ⟨a', b, c, d, he, Or.inr ha, Or.inl (.refl _), Or.inl (.refl _), Or.inl (.refl _)⟩
  · exact ⟨a, b', c, d, he, Or.inl (.refl _), Or.inr hb, Or.inl (.refl _), Or.inl (.refl _)⟩
  · exact ⟨a, b, c', d, he, Or.inl (.refl _), Or.inl (.refl _), Or.inr hc, Or.inl (.refl _)⟩
  · exact ⟨a, b, c, d', he, Or.inl (.refl _), Or.inl (.refl _), Or.inl (.refl _), Or.inr hd⟩

/-- Proof construction inherits local confluence from all four components. -/
theorem locally_confluent_at_spk (a b c d : Term V)
    (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b)
    (hc : LocallyConfluentAt c) (hd : LocallyConfluentAt d) : LocallyConfluentAt (.spk a b c d) := by
  intro u v hu hv
  obtain ⟨a₁, b₁, c₁, d₁, he₁, ha₁, hb₁, hc₁, hd₁⟩ := hu.spk_components
  obtain ⟨a₂, b₂, c₂, d₂, he₂, ha₂, hb₂, hc₂, hd₂⟩ := hv.spk_components
  exact (JoinModulo.spk (ha.base_or_step ha₁ ha₂) (hb.base_or_step hb₁ hb₂)
    (hc.base_or_step hc₁ hc₂) (hd.base_or_step hd₁ hd₂)).of_base he₁ he₂

end ExplainableCrypto.Helios.Symbolic
