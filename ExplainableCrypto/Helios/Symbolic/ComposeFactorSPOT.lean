import ExplainableCrypto.Helios.Symbolic.ComposeLocalConfluence
import ExplainableCrypto.Helios.Symbolic.AtomIrreducibility

namespace ExplainableCrypto.Helios.Symbolic.ComposeFactorSPOT

/-- The reconstruction instance was local: exported multiplication is unchanged. -/
theorem multiplication_instance_unchanged (a b : Term Nat) :
    a.baseClass * b.baseClass = (Term.binary .mul a b).baseClass := rfl

theorem zero_not_composition_unit :
    ¬ BaseEq (Term.binary .compose (.name 0) (.const .zero) : Term Nat) (.name 0) := by
  intro h
  cases h.head_eq

theorem repeated_composition_factor_retained :
    (Term.binary .compose (.name 0) (.name 0) : Term Nat).composeFactors.card = 2 ∧
    ¬ BaseEq (Term.binary .compose (.name 0) (.name 0) : Term Nat) (.name 0) := by
  refine ⟨by decide, ?_⟩
  intro h
  have hc := congrArg Multiset.card h.compose_factors
  simp [Term.composeFactors] at hc

abbrev outA : Term Nat := .binary .compose (.name 1) (.name 2)
abbrev outB : Term Nat := .binary .compose (.name 3) (.name 4)
abbrev a : Term Nat := .unary .fst (.binary .pair outA (.const .bottom))
abbrev b : Term Nat := .unary .snd (.binary .pair (.const .bottom) outB)
abbrev source : Term Nat := .binary .compose (.binary .compose a (.name 9)) b
abbrev left : Term Nat := .binary .compose (.binary .compose outA (.name 9)) b
abbrev right : Term Nat := .binary .compose (.binary .compose a (.name 9)) outB
abbrev expected : Term Nat := .binary .compose (.binary .compose outA (.name 9)) outB

private theorem bag_swap (a b c : Multiset (BaseClass Nat)) : a + (b + c) = b + (a + c) := by
  rw [← Multiset.add_assoc, Multiset.add_comm a b, Multiset.add_assoc]

/-- Nonadjacent disjoint projections expand to two factors each and retain name 9. -/
theorem disjoint_expanding_projections :
    ModuloStep source left ∧ ModuloStep source right ∧ JoinModulo left right ∧
    left.composeFactors.card = 4 ∧ right.composeFactors.card = 4 ∧
    expected.composeFactors.card = 5 ∧ left ≠ right := by
  have h := disjoint_compose_reductions_joined source left right a outA b outB
    {(Term.name 9 : Term Nat).baseClass}
    (RootStep.fst outA (.const .bottom)).to_modulo
    (RootStep.snd (.const .bottom) outB).to_modulo
    (by simp only [Term.composeFactors, Multiset.add_assoc, Multiset.add_comm, bag_swap])
    (by simp only [Term.composeFactors, Multiset.add_assoc, Multiset.add_comm])
    (by simp only [Term.composeFactors, Multiset.add_assoc, Multiset.add_comm])
  exact ⟨h.1, h.2.1, h.2.2, by decide, by decide, by decide, by decide⟩

/-- Independent fixed common descendant; both output compositions remain intact. -/
theorem disjoint_routes_expected : ModuloStep left expected ∧ ModuloStep right expected :=
  ⟨(RootStep.snd (.const .bottom) outB).to_modulo.context
    (.binaryRight .compose (.binary .compose outA (.name 9)) .hole),
    (RootStep.fst outA (.const .bottom)).to_modulo.context
      (.binaryLeft .compose (.binaryLeft .compose .hole (.name 9)) outB)⟩

/-- An empty remainder has no object-language sentinel. -/
theorem empty_remainder_expansion : ModuloStep a outA ∧
    a.composeFactors.card = 1 ∧ outA.composeFactors.card = 2 :=
  ⟨(RootStep.fst outA (.const .bottom)).to_modulo.of_compose_factors 0 (by simp) (by simp),
    by decide, by decide⟩

abbrev aReversed : Term Nat := .unary .fst
  (.binary .pair (.binary .compose (.name 2) (.name 1)) (.const .bottom))

theorem representative_change_retains_remainder :
    ModuloStep (.binary .compose aReversed (.name 9)) (.binary .compose outA (.name 9)) := by
  have he : BaseEq aReversed a := .unary .fst (.binary .pair
    (.equation (.comm .compose trivial _ _)) (.refl _))
  apply (RootStep.fst outA (.const .bottom)).to_modulo.of_compose_factors {(Term.name 9 : Term Nat).baseClass}
  · simpa only [Term.composeFactors] using congrArg
      (fun q => ({q} : Multiset (BaseClass Nat)) + {(Term.name 9 : Term Nat).baseClass})
        ((baseClass_eq_iff _ _).mpr he)
  · rfl

abbrev c₁ : Term Nat := .ternary .penc (.name 0) (.name 1) (.const .zero)
abbrev c₂ : Term Nat := .ternary .penc (.name 0) (.name 2) (.const .one)
abbrev combined : Term Nat := combinedCiphertext (.name 0) (.name 1) (.name 2) (.const .zero) (.const .one)

/-- E7 is a multiplication rule, not a nonce-composition rule. -/
theorem composition_and_multiplication_differ :
    (rootReduce (.binary .compose c₁ c₂)).isNone = true ∧
    (rootReduce (.binary .mul c₁ c₂)).map Subtype.val = some combined ∧
    ¬ BaseEq (.binary .compose c₁ c₂) (.binary .mul c₁ c₂) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  cases h.head_eq

/-- The multiplication root is one composition-factor replacement under a compose context. -/
theorem multiplication_inside_composition :
    ComposeFactorStep (.binary .compose (.binary .mul c₁ c₂) (.name 9))
      (.binary .compose combined (.name 9)) ∧
    (Term.binary .compose (.binary .mul c₁ c₂) (.name 9)).composeFactors.card = 2 ∧
    (Term.binary .compose combined (.name 9)).composeFactors.card = 2 :=
  ⟨((RootStep.homomorphic (.name 0) (.name 1) (.name 2) (.const .zero) (.const .one)).to_modulo.context
    (.binaryLeft .compose .hole (.name 9))).compose_factor, by decide, by decide⟩

theorem composed_names_irreducible (n m : Nat) :
    Irreducible (Term.binary .compose (.name n) (.name m) : Term Nat) := by
  apply irreducible_of_compose_factors
  intro t _ ht
  simp only [Term.composeFactors, Multiset.mem_add, Multiset.mem_singleton] at ht
  rcases ht with ht | ht
  · exact (name_irreducible n).base ((baseClass_eq_iff _ _).mp ht).symm
  · exact (name_irreducible m).base ((baseClass_eq_iff _ _).mp ht).symm

/-- Instantiate the factor-local premise with independently locally confluent
projection factors. Actual distinct first steps exclude a no-peak interpretation. -/
theorem composition_source_locally_confluent : LocallyConfluentAt source ∧
    ModuloStep source left ∧ ModuloStep source right ∧ left ≠ right := by
  have ha : LocallyConfluentAt a := locally_confluent_at_unary .fst _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (composed_names_irreducible 1 2).locally_confluent_at (constant_irreducible .bottom).locally_confluent_at)
  have hb : LocallyConfluentAt b := locally_confluent_at_unary .snd _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (constant_irreducible .bottom).locally_confluent_at (composed_names_irreducible 3 4).locally_confluent_at)
  have hl : ComposeFactorsLocallyConfluent source := by
    apply compose_factors_local_of_representatives
    intro q hq
    simp only [Term.composeFactors, Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with (rfl | rfl) | rfl
    · exact ⟨a, rfl, ha⟩
    · exact ⟨.name 9, rfl, (name_irreducible 9).locally_confluent_at⟩
    · exact ⟨b, rfl, hb⟩
  exact ⟨locally_confluent_at_of_compose_factors source hl,
    disjoint_expanding_projections.1, disjoint_expanding_projections.2.1,
    disjoint_expanding_projections.2.2.2.2.2.2⟩

end ExplainableCrypto.Helios.Symbolic.ComposeFactorSPOT
