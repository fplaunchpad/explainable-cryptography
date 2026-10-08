import ExplainableCrypto.Helios.Symbolic.AtomIrreducibility

namespace ExplainableCrypto.Helios.Symbolic.UnaryLocalSPOT

abbrev first : Term Nat := .unary .fst (.binary .pair (.name 0) (.name 1))
abbrev second : Term Nat := .unary .snd (.binary .pair (.name 2) (.name 3))
abbrev source : Term Nat := .unary .fst (.binary .pair first second)
abbrev changed : Term Nat := .unary .fst (.binary .pair (.name 0) second)

theorem first_local : LocallyConfluentAt first :=
  locally_confluent_at_unary .fst _ (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
    (name_irreducible 0).locally_confluent_at (name_irreducible 1).locally_confluent_at)

theorem second_local : LocallyConfluentAt second :=
  locally_confluent_at_unary .snd _ (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
    (name_irreducible 2).locally_confluent_at (name_irreducible 3).locally_confluent_at)

/-- All modulo peaks from this nested projection join, with no local-confluence
premise left in this instantiated statement. Its explicit branches rule out no-step vacuity. -/
theorem nested_projection_local : LocallyConfluentAt source ∧
    ModuloStep source first ∧ ModuloStep source changed ∧ JoinModulo first changed ∧ first ≠ changed := by
  have hl : LocallyConfluentAt source := locally_confluent_at_unary .fst _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _ first_local second_local)
  have hr := (RootStep.fst first second).to_modulo
  have hi : ModuloStep source changed := (RootStep.fst (.name 0) (.name 1)).to_modulo.context
    (.unary .fst (.binaryLeft .pair .hole second))
  exact ⟨hl, hr, hi, hl _ _ hr hi, by decide⟩

/-- Independently specified descendant for the selected-member fixture. -/
theorem nested_routes_expected : ModuloStep first (.name 0) ∧ ModuloStep changed (.name 0) :=
  ⟨(RootStep.fst (.name 0) (.name 1)).to_modulo, (RootStep.fst (.name 0) second).to_modulo⟩

/-- Both projections, and both pair positions, follow the selected member or
discard the changed member according to the source E1/E2 equations. -/
theorem four_projection_mixed_joins :
    JoinModulo first (.unary .fst (.binary .pair (.name 0) (.name 2))) ∧
    JoinModulo (V := Nat) (.name 2) (.unary .snd (.binary .pair (.name 0) (.name 2))) ∧
    JoinModulo (V := Nat) (.name 2) (.unary .fst (.binary .pair (.name 2) (.name 0))) ∧
    JoinModulo first (.unary .snd (.binary .pair (.name 2) (.name 0))) := by
  have h := (RootStep.fst (V := Nat) (.name 0) (.name 1)).to_modulo
  exact ⟨fst_pair_step_joined first (.name 2) (h.context (.binaryLeft .pair .hole (.name 2))),
    snd_pair_step_joined first (.name 2) (h.context (.binaryLeft .pair .hole (.name 2))),
    fst_pair_step_joined (.name 2) first (h.context (.binaryRight .pair (.name 2) .hole)),
    snd_pair_step_joined (.name 2) first (h.context (.binaryRight .pair (.name 2) .hole))⟩

abbrev expandedZero : Term Nat := .binary .add (.const .zero) (.const .zero)

/-- Root and internal branches may independently change E0 representatives. -/
theorem background_projection_peak :
    let a : Term Nat := .binary .pair (.const .zero) first
    let b : Term Nat := .binary .pair expandedZero (.name 0)
    RootModuloStep (.unary .fst a) expandedZero ∧ ModuloStep a b ∧
      JoinModulo expandedZero (.unary .fst b) := by
  have hr : RootModuloStep (.unary .fst (.binary .pair (.const .zero) first)) expandedZero :=
    ⟨_, _, .refl _, .fst (.const .zero) first, (BaseEq.equation .zero_zero).symm⟩
  have hi : ModuloStep (.binary .pair (.const .zero) first)
      (.binary .pair expandedZero (.name 0)) :=
    ((RootStep.fst (.name 0) (.name 1)).to_modulo.context
      (.binaryRight .pair (.const .zero) .hole)).post_base
        (.binary .pair (BaseEq.equation .zero_zero).symm (.refl _))
  exact ⟨hr, hi, unary_root_inner_joined hr hi⟩

/-- Ordered pairing cannot be treated as an AC operator. -/
theorem pair_order_not_base :
    ¬ BaseEq (Term.binary .pair (.name 0) (.name 1) : Term Nat) (.binary .pair (.name 1) (.name 0)) := by
  intro h
  obtain ⟨_, hn, _⟩ := (BaseEq.binary_iff .pair .pair (by simp [AC]) (by simp [AC]) _ _ _ _).mp h
  have he := (BaseEq.name_iff _ _).mp hn
  omega

/-- The minimized false projection-equality test is retained in Lean. -/
theorem projection_outputs_differ :
    (rootReduce first).map Subtype.val = some (.name 0) ∧
    (rootReduce (Term.unary .snd (.binary .pair (.name 0) (.name 1)) : Term Nat)).map Subtype.val = some (.name 1) ∧
    (Term.name 0 : Term Nat) ≠ .name 1 := by decide

/-- No root match under pk coexists with actual contextual progress and local confluence. -/
theorem pk_local_nonvacuous : LocallyConfluentAt (.unary .pk first) ∧
    ModuloStep (.unary .pk first) (.unary .pk (.name 0)) ∧
    (rootReduce (.unary .pk first)).isNone = true :=
  ⟨locally_confluent_at_unary .pk first first_local,
    (RootStep.fst (.name 0) (.name 1)).to_modulo.context (.unary .pk .hole), by decide⟩

/-- The passive partial-decryption constructor preserves both component reductions. -/
theorem partial_decrypt_component_peak :
    let a := Term.binary .partialDecrypt first second
    let b := Term.binary .partialDecrypt (.name 0) second
    let c := Term.binary .partialDecrypt first (.name 3)
    LocallyConfluentAt a ∧ ModuloStep a b ∧ ModuloStep a c ∧ JoinModulo b c ∧ b ≠ c := by
  have hl := locally_confluent_at_passive_binary .partialDecrypt (Or.inr rfl)
    first second first_local second_local
  have hb := (RootStep.fst (V := Nat) (.name 0) (.name 1)).to_modulo.context
    (.binaryLeft .partialDecrypt .hole second)
  have hc := (RootStep.snd (V := Nat) (.name 2) (.name 3)).to_modulo.context
    (.binaryRight .partialDecrypt first .hole)
  exact ⟨hl, hb, hc, hl _ _ hb hc, by decide⟩

end ExplainableCrypto.Helios.Symbolic.UnaryLocalSPOT
