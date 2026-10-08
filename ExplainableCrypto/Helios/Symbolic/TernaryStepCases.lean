import ExplainableCrypto.Helios.Symbolic.ProofStepCases

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem BaseEq.ternary_shape {f : Ternary} {a b c t : Term V} (h : BaseEq (.ternary f a b c) t) :
    ∃ a' b' c', t = .ternary f a' b' c' ∧ BaseEq a a' ∧ BaseEq b b' ∧ BaseEq c c' := by
  have hh := h.head_eq
  cases t with
  | name => cases hh
  | var => cases hh
  | const d => cases d <;> cases hh
  | unary => cases hh
  | binary g => cases g <;> cases hh
  | ternary g a' b' c' =>
    obtain ⟨rfl, ha, hb, hc⟩ := (BaseEq.ternary_iff _ _ _ _ _ _ _ _).mp h
    exact ⟨a', b', c', rfl, ha, hb, hc⟩
  | spk => cases hh

theorem RewriteStep.ternary_cases {f : Ternary} {a b c t : Term V}
    (h : RewriteStep (.ternary f a b c) t) :
    RootStep (.ternary f a b c) t ∨
    (∃ a', RewriteStep a a' ∧ t = .ternary f a' b c) ∨
    (∃ b', RewriteStep b b' ∧ t = .ternary f a b' c) ∨
    (∃ c', RewriteStep c c' ∧ t = .ternary f a b c') := by
  obtain ⟨ctx, l, r, hr, hs, rfl⟩ := h
  cases ctx with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    exact Or.inl hr
  | ternaryFirst g ctx x y =>
    simp only [Context.fill, Term.ternary.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inl ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩)
  | ternarySecond g x ctx y =>
    simp only [Context.fill, Term.ternary.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inr (Or.inl ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩))
  | ternaryThird g x y ctx =>
    simp only [Context.fill, Term.ternary.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inr (Or.inr ⟨ctx.fill r, ⟨ctx, l, r, hr, rfl, rfl⟩, rfl⟩))
  | _ => cases hs

/-- One actual argument step, with the full target allowed to change E0 representative. -/
def TernaryArgumentStep (f : Ternary) (a b c t : Term V) : Prop :=
  (∃ a', ModuloStep a a' ∧ BaseEq t (.ternary f a' b c)) ∨
  (∃ b', ModuloStep b b' ∧ BaseEq t (.ternary f a b' c)) ∨
  (∃ c', ModuloStep c c' ∧ BaseEq t (.ternary f a b c'))

/-- All ternary modulo steps, including active proof-checking roots. -/
theorem ModuloStep.ternary_cases {f : Ternary} {a b c t : Term V}
    (h : ModuloStep (.ternary f a b c) t) :
    RootModuloStep (.ternary f a b c) t ∨ TernaryArgumentStep f a b c t := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  obtain ⟨a₀, b₀, c₀, rfl, ha, hb, hc⟩ := hx.ternary_shape
  rcases hxy.ternary_cases with hr | ⟨a', hs, rfl⟩ | ⟨b', hs, rfl⟩ | ⟨c', hs, rfl⟩
  · exact Or.inl ⟨_, _, hx, hr, hy⟩
  · exact Or.inr (Or.inl ⟨a', ⟨a₀, a', ha, hs, .refl _⟩,
      hy.symm.trans (.ternary f (.refl _) hb.symm hc.symm)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b', ⟨b₀, b', hb, hs, .refl _⟩,
      hy.symm.trans (.ternary f ha.symm (.refl _) hc.symm)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c', ⟨c₀, c', hc, hs, .refl _⟩,
      hy.symm.trans (.ternary f ha.symm hb.symm (.refl _))⟩))

theorem TernaryArgumentStep.components {f : Ternary} {a b c t : Term V}
    (h : TernaryArgumentStep f a b c t) :
    ∃ a' b' c', BaseEq t (.ternary f a' b' c') ∧
      (BaseEq a a' ∨ ModuloStep a a') ∧ (BaseEq b b' ∨ ModuloStep b b') ∧
      (BaseEq c c' ∨ ModuloStep c c') := by
  rcases h with ⟨a', ha, he⟩ | ⟨b', hb, he⟩ | ⟨c', hc, he⟩
  · exact ⟨a', b, c, he, Or.inr ha, Or.inl (.refl _), Or.inl (.refl _)⟩
  · exact ⟨a, b', c, he, Or.inl (.refl _), Or.inr hb, Or.inl (.refl _)⟩
  · exact ⟨a, b, c', he, Or.inl (.refl _), Or.inl (.refl _), Or.inr hc⟩

theorem ternary_argument_peaks_joined (f : Ternary) (a b c : Term V)
    (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b) (hc : LocallyConfluentAt c)
    {u v : Term V} (hu : TernaryArgumentStep f a b c u) (hv : TernaryArgumentStep f a b c v) :
    JoinModulo u v := by
  obtain ⟨a₁, b₁, c₁, he₁, ha₁, hb₁, hc₁⟩ := hu.components
  obtain ⟨a₂, b₂, c₂, he₂, ha₂, hb₂, hc₂⟩ := hv.components
  exact (JoinModulo.ternary f (ha.base_or_step ha₁ ha₂) (hb.base_or_step hb₁ hb₂)
    (hc.base_or_step hc₁ hc₂)).of_base he₁ he₂

/-- The root/internal obligation is explicit and must be discharged for each active symbol. -/
theorem locally_confluent_at_ternary (f : Ternary) (a b c : Term V)
    (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b) (hc : LocallyConfluentAt c)
    (hmixed : ∀ u v, RootModuloStep (.ternary f a b c) u →
      TernaryArgumentStep f a b c v → JoinModulo u v) : LocallyConfluentAt (.ternary f a b c) := by
  intro u v hu hv
  rcases hu.ternary_cases with hu | hu
  · rcases hv.ternary_cases with hv | hv
    · exact ⟨v, .base (hu.outputs_base hv), .refl _⟩
    · exact hmixed _ _ hu hv
  · rcases hv.ternary_cases with hv | hv
    · exact (hmixed _ _ hv hu).symm
    · exact ternary_argument_peaks_joined f a b c ha hb hc hu hv

end ExplainableCrypto.Helios.Symbolic
