import ExplainableCrypto.Helios.Symbolic.GlobalConfluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem base_or_step_reduces {a b : Term V} (h : BaseEq a b ∨ ModuloStep a b) :
    ReducesModulo a b := h.elim ReducesModulo.base ReducesModulo.single

private theorem penc_path {s t : Term V} (h : ReducesModulo s t) {k r m : Term V}
    (he : BaseEq s (.ternary .penc k r m)) :
    ∃ k' r' m', BaseEq t (.ternary .penc k' r' m') ∧
      ReducesModulo k k' ∧ ReducesModulo r r' ∧ ReducesModulo m m' := by
  induction h generalizing k r m with
  | base hb => exact ⟨k, r, m, hb.symm.trans he, .refl _, .refl _, .refl _⟩
  | head hs _ ih =>
    obtain ⟨k₁, r₁, m₁, ht, hk, hr, hm⟩ := (hs.pre_base he.symm).penc_components
    obtain ⟨k₂, r₂, m₂, ht₂, hk₂, hr₂, hm₂⟩ := ih ht
    exact ⟨k₂, r₂, m₂, ht₂, (base_or_step_reduces hk).trans hk₂,
      (base_or_step_reduces hr).trans hr₂, (base_or_step_reduces hm).trans hm₂⟩

/-- Every ciphertext path preserves its constructor and ordered component paths,
including E0 changes at both ends and zero oriented steps. -/
theorem ReducesModulo.penc_components {k r m t : Term V}
    (h : ReducesModulo (.ternary .penc k r m) t) :
    ∃ k' r' m', BaseEq t (.ternary .penc k' r' m') ∧
      ReducesModulo k k' ∧ ReducesModulo r r' ∧ ReducesModulo m m' := penc_path h (.refl _)

private theorem spk_path {s t : Term V} (h : ReducesModulo s t) {a b c d : Term V}
    (he : BaseEq s (.spk a b c d)) :
    ∃ a' b' c' d', BaseEq t (.spk a' b' c' d') ∧
      ReducesModulo a a' ∧ ReducesModulo b b' ∧ ReducesModulo c c' ∧ ReducesModulo d d' := by
  induction h generalizing a b c d with
  | base hb => exact ⟨a, b, c, d, hb.symm.trans he, .refl _, .refl _, .refl _, .refl _⟩
  | head hs _ ih =>
    obtain ⟨a₁, b₁, c₁, d₁, ht, ha, hb, hc, hd⟩ := (hs.pre_base he.symm).spk_components
    obtain ⟨a₂, b₂, c₂, d₂, ht₂, ha₂, hb₂, hc₂, hd₂⟩ := ih ht
    exact ⟨a₂, b₂, c₂, d₂, ht₂, (base_or_step_reduces ha).trans ha₂,
      (base_or_step_reduces hb).trans hb₂, (base_or_step_reduces hc).trans hc₂,
      (base_or_step_reduces hd).trans hd₂⟩

theorem ReducesModulo.spk_components {a b c d t : Term V}
    (h : ReducesModulo (.spk a b c d) t) :
    ∃ a' b' c' d', BaseEq t (.spk a' b' c' d') ∧
      ReducesModulo a a' ∧ ReducesModulo b b' ∧ ReducesModulo c c' ∧ ReducesModulo d d' :=
  spk_path h (.refl _)

private theorem passive_binary_path {f : Binary} (hf : f = .pair ∨ f = .partialDecrypt)
    {s t : Term V} (h : ReducesModulo s t) {a b : Term V}
    (he : BaseEq s (.binary f a b)) :
    ∃ a' b', BaseEq t (.binary f a' b') ∧ ReducesModulo a a' ∧ ReducesModulo b b' := by
  induction h generalizing a b with
  | base hb => exact ⟨a, b, hb.symm.trans he, .refl _, .refl _⟩
  | head hs _ ih =>
    obtain ⟨a₁, b₁, ht, ha, hb⟩ := (hs.pre_base he.symm).passive_binary_components hf
    obtain ⟨a₂, b₂, ht₂, ha₂, hb₂⟩ := ih ht
    exact ⟨a₂, b₂, ht₂, (base_or_step_reduces ha).trans ha₂, (base_or_step_reduces hb).trans hb₂⟩

theorem ReducesModulo.passive_binary_components {f : Binary} (hf : f = .pair ∨ f = .partialDecrypt)
    {a b t : Term V} (h : ReducesModulo (.binary f a b) t) :
    ∃ a' b', BaseEq t (.binary f a' b') ∧ ReducesModulo a a' ∧ ReducesModulo b b' :=
  passive_binary_path hf h (.refl _)

end ExplainableCrypto.Helios.Symbolic
