import ExplainableCrypto.Helios.Symbolic.FactorPeak
import ExplainableCrypto.Helios.Symbolic.ReductionSubstitution

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Local confluence at one specified source, with arbitrary modulo endpoints. -/
def LocallyConfluentAt (a : Term V) : Prop :=
  ∀ b c, ModuloStep a b → ModuloStep a c → JoinModulo b c

theorem JoinModulo.of_base {a b u v : Term V} (h : JoinModulo a b)
    (hu : BaseEq u a) (hv : BaseEq v b) : JoinModulo u v := by
  obtain ⟨w, ha, hb⟩ := h
  exact ⟨w, ha.pre_base hu, hb.pre_base hv⟩

/-- Include unchanged E0 representatives when combining component cases. -/
theorem LocallyConfluentAt.base_or_step {a b c : Term V} (hl : LocallyConfluentAt a)
    (hb : BaseEq a b ∨ ModuloStep a b) (hc : BaseEq a c ∨ ModuloStep a c) :
    JoinModulo b c := by
  rcases hb with hb | hb
  · rcases hc with hc | hc
    · exact ⟨c, .base (hb.symm.trans hc), .refl _⟩
    · exact ⟨c, (ReducesModulo.single hc).pre_base hb.symm, .refl _⟩
  · rcases hc with hc | hc
    · exact ⟨b, .refl _, (ReducesModulo.single hb).pre_base hc.symm⟩
    · exact hl b c hb hc

theorem JoinModulo.ternary (f : Ternary) {a a' b b' c c' : Term V}
    (ha : JoinModulo a a') (hb : JoinModulo b b') (hc : JoinModulo c c') :
    JoinModulo (.ternary f a b c) (.ternary f a' b' c') := by
  obtain ⟨x, hax, hax'⟩ := ha
  obtain ⟨y, hby, hby'⟩ := hb
  obtain ⟨z, hcz, hcz'⟩ := hc
  exact ⟨.ternary f x y z, .ternary f hax hby hcz, .ternary f hax' hby' hcz'⟩

/-- A consequence of exhaustive inversion that packages the untouched components
as E0 steps. This packaging alone does not assert local confluence. -/
theorem ModuloStep.penc_components {k r m t : Term V}
    (h : ModuloStep (.ternary .penc k r m) t) :
    ∃ k' r' m', BaseEq t (.ternary .penc k' r' m') ∧
      (BaseEq k k' ∨ ModuloStep k k') ∧
      (BaseEq r r' ∨ ModuloStep r r') ∧
      (BaseEq m m' ∨ ModuloStep m m') := by
  rcases h.penc_cases with ⟨k', hk, he⟩ | ⟨r', hr, he⟩ | ⟨m', hm, he⟩
  · exact ⟨k', r, m, he, Or.inr hk, Or.inl (.refl _), Or.inl (.refl _)⟩
  · exact ⟨k, r', m, he, Or.inl (.refl _), Or.inr hr, Or.inl (.refl _)⟩
  · exact ⟨k, r, m', he, Or.inl (.refl _), Or.inl (.refl _), Or.inr hm⟩

/-- The ciphertext case reduces to its three component sources, each with an
explicit local-confluence hypothesis. Other constructor cases remain separate. -/
theorem locally_confluent_at_penc (k r m : Term V)
    (hk : LocallyConfluentAt k) (hr : LocallyConfluentAt r) (hm : LocallyConfluentAt m) :
    LocallyConfluentAt (.ternary .penc k r m) := by
  intro b c hb hc
  obtain ⟨k₁, r₁, m₁, he₁, hk₁, hr₁, hm₁⟩ := hb.penc_components
  obtain ⟨k₂, r₂, m₂, he₂, hk₂, hr₂, hm₂⟩ := hc.penc_components
  exact (JoinModulo.ternary .penc (hk.base_or_step hk₁ hk₂)
    (hr.base_or_step hr₁ hr₂) (hm.base_or_step hm₁ hm₂)).of_base he₁ he₂

/-- Different component steps commute unconditionally, exposing the exact common
endpoint rather than requiring local confluence for either component. -/
theorem ciphertext_key_nonce_steps (k k' r r' m : Term V)
    (hk : ModuloStep k k') (hr : ModuloStep r r') :
    ModuloStep (.ternary .penc k r m) (.ternary .penc k' r m) ∧
    ModuloStep (.ternary .penc k r m) (.ternary .penc k r' m) ∧
    ModuloStep (.ternary .penc k' r m) (.ternary .penc k' r' m) ∧
    ModuloStep (.ternary .penc k r' m) (.ternary .penc k' r' m) :=
  ⟨hk.context (.ternaryFirst .penc .hole r m), hr.context (.ternarySecond .penc k .hole m),
    hr.context (.ternarySecond .penc k' .hole m), hk.context (.ternaryFirst .penc .hole r' m)⟩

end ExplainableCrypto.Helios.Symbolic
