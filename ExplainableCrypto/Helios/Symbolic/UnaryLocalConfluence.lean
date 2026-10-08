import ExplainableCrypto.Helios.Symbolic.RigidStepCases

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- The only unary-root rules are the two ordered projections. -/
theorem RootModuloStep.unary_projection_cases {f : Unary} {a t : Term V}
    (h : RootModuloStep (.unary f a) t) :
    (∃ x y, f = .fst ∧ BaseEq a (.binary .pair x y) ∧ BaseEq x t) ∨
    (∃ x y, f = .snd ∧ BaseEq a (.binary .pair x y) ∧ BaseEq y t) := by
  obtain ⟨l, r, he, hr, ht⟩ := h
  cases hr with
  | fst x y =>
    obtain ⟨hf, ha⟩ := (BaseEq.unary_iff _ _ _ _).mp he
    exact Or.inl ⟨_, _, hf, ha, ht⟩
  | snd x y =>
    obtain ⟨hf, ha⟩ := (BaseEq.unary_iff _ _ _ _).mp he
    exact Or.inr ⟨_, _, hf, ha, ht⟩
  | _ => have hh := he.head_eq; cases hh

/-- A first projection competes with every step inside its pair. Reducing a
selected member is followed on both routes; reducing a discarded member is erased. -/
theorem fst_pair_step_joined (x y : Term V) {t : Term V}
    (h : ModuloStep (.binary .pair x y) t) : JoinModulo x (.unary .fst t) := by
  rcases h.passive_binary_cases (Or.inl rfl) with ⟨x', hx, he⟩ | ⟨y', hy, he⟩
  · exact ⟨x', .single hx,
      .single ((RootStep.fst x' y).to_modulo.pre_base (.unary .fst he))⟩
  · exact ⟨x, .refl _,
      .single ((RootStep.fst x y').to_modulo.pre_base (.unary .fst he))⟩

/-- Second projection follows the second member and discards changes in the first. -/
theorem snd_pair_step_joined (x y : Term V) {t : Term V}
    (h : ModuloStep (.binary .pair x y) t) : JoinModulo y (.unary .snd t) := by
  rcases h.passive_binary_cases (Or.inl rfl) with ⟨x', hx, he⟩ | ⟨y', hy, he⟩
  · exact ⟨y, .refl _,
      .single ((RootStep.snd x' y).to_modulo.pre_base (.unary .snd he))⟩
  · exact ⟨y', .single hy,
      .single ((RootStep.snd x y').to_modulo.pre_base (.unary .snd he))⟩

/-- Unary root versus arbitrary argument reduction, with E0 source and target changes. -/
theorem unary_root_inner_joined {f : Unary} {a b a' : Term V}
    (hb : RootModuloStep (.unary f a) b) (ha : ModuloStep a a') :
    JoinModulo b (.unary f a') := by
  rcases hb.unary_projection_cases with ⟨x, y, rfl, he, ht⟩ | ⟨x, y, rfl, he, ht⟩
  · exact (fst_pair_step_joined x y (ha.pre_base he.symm)).of_base ht.symm (.refl _)
  · exact (snd_pair_step_joined x y (ha.pre_base he.symm)).of_base ht.symm (.refl _)

/-- All unary operators, including both active projections and pk. Only the
argument's local confluence is required; root/internal joins are proved above. -/
theorem locally_confluent_at_unary (f : Unary) (a : Term V)
    (ha : LocallyConfluentAt a) : LocallyConfluentAt (.unary f a) := by
  intro b c hb hc
  rcases hb.unary_cases with hb | ⟨b', hb, heb⟩
  · rcases hc.unary_cases with hc | ⟨c', hc, hec⟩
    · exact ⟨c, .base (hb.outputs_base hc), .refl _⟩
    · exact (unary_root_inner_joined hb hc).of_base (.refl _) hec
  · rcases hc.unary_cases with hc | ⟨c', hc, hec⟩
    · exact ((unary_root_inner_joined hc hb).of_base (.refl _) heb).symm
    · exact ((ha b' c' hb hc).context (.unary f .hole)).of_base heb hec

theorem JoinModulo.binary (f : Binary) {a a' b b' : Term V}
    (ha : JoinModulo a a') (hb : JoinModulo b b') :
    JoinModulo (.binary f a b) (.binary f a' b') := by
  obtain ⟨x, hax, hax'⟩ := ha
  obtain ⟨y, hby, hby'⟩ := hb
  exact ⟨.binary f x y, .binary f hax hby, .binary f hax' hby'⟩

/-- Package passive binary changes while preserving E0-equivalent untouched arguments. -/
theorem ModuloStep.passive_binary_components {f : Binary} (hf : f = .pair ∨ f = .partialDecrypt)
    {a b t : Term V} (h : ModuloStep (.binary f a b) t) :
    ∃ a' b', BaseEq t (.binary f a' b') ∧
      (BaseEq a a' ∨ ModuloStep a a') ∧ (BaseEq b b' ∨ ModuloStep b b') := by
  rcases h.passive_binary_cases hf with ⟨a', ha, he⟩ | ⟨b', hb, he⟩
  · exact ⟨a', b, he, Or.inr ha, Or.inl (.refl _)⟩
  · exact ⟨a, b', he, Or.inl (.refl _), Or.inr hb⟩

/-- Pairing and partial-decryption construction inherit local confluence from
their two arguments. Active decryption and the AC operators are outside this lemma. -/
theorem locally_confluent_at_passive_binary (f : Binary) (hf : f = .pair ∨ f = .partialDecrypt)
    (a b : Term V) (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b) :
    LocallyConfluentAt (.binary f a b) := by
  intro u v hu hv
  obtain ⟨a₁, b₁, he₁, ha₁, hb₁⟩ := hu.passive_binary_components hf
  obtain ⟨a₂, b₂, he₂, ha₂, hb₂⟩ := hv.passive_binary_components hf
  exact (JoinModulo.binary f (ha.base_or_step ha₁ ha₂)
    (hb.base_or_step hb₁ hb₂)).of_base he₁ he₂

end ExplainableCrypto.Helios.Symbolic
