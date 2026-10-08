import ExplainableCrypto.Helios.Symbolic.AdditionLocalConfluence
import ExplainableCrypto.Helios.Symbolic.AtomIrreducibility

namespace ExplainableCrypto.Helios.Symbolic.AdditionReplacementSPOT

abbrev zero : Term Nat := .const .zero
abbrev one : Term Nat := .const .one
abbrev marker : Term Nat := .name 9
abbrev a : Term Nat := .unary .fst (.binary .pair one (.const .bottom))
abbrev b : Term Nat := .unary .snd (.binary .pair (.const .bottom) zero)
abbrev source : Term Nat := .binary .add (.binary .add a marker) (.binary .add b zero)
abbrev left : Term Nat := .binary .add (.binary .add one marker) (.binary .add b zero)
abbrev right : Term Nat := .binary .add (.binary .add a marker) (.binary .add zero zero)
abbrev expected : Term Nat := .binary .add one marker

private theorem summary_swap (a b c : AddSummary (BaseClass Nat)) :
    a.combine (b.combine c) = b.combine (a.combine c) := by
  rw [← AddSummary.combine_assoc, AddSummary.combine_comm a b, AddSummary.combine_assoc]

/-- Independent projections introduce numeric one and zero in different orders. -/
theorem disjoint_numeric_projections :
    ModuloStep source left ∧ ModuloStep source right ∧ JoinModulo left right := by
  apply disjoint_add_reductions_joined source left right a one b zero
    (marker.addSummary.combine zero.addSummary)
    (RootStep.fst one (.const .bottom)).to_modulo
    (RootStep.snd (.const .bottom) zero).to_modulo
  all_goals simp only [Term.addSummary, AddSummary.combine_assoc, summary_swap, AddSummary.combine_comm]

/-- Exact endpoints exclude a join obtained by erasing the retained name or one. -/
theorem disjoint_routes_expected : ModuloStep left expected ∧ ModuloStep right expected := by
  have he : BaseEq (.binary .add (.binary .add one marker) (.binary .add zero zero)) expected := by
    apply (baseEq_iff_addSummary _ _).mpr
    simp [Term.addSummary, AddSummary.combine, AddSummary.atom, AddSummary.number, numericAdd]
  exact ⟨((RootStep.snd (.const .bottom) zero).to_modulo.context
    (.binaryRight .add (.binary .add one marker) (.binaryLeft .add .hole zero))).post_base he,
    ((RootStep.fst one (.const .bottom)).to_modulo.context
      (.binaryLeft .add (.binaryLeft .add .hole marker) (.binary .add zero zero))).post_base he⟩

theorem numeric_presence_changes : source.addSummary.numeric = some 0 ∧
    left.addSummary.numeric = some 1 ∧ right.addSummary.numeric = some 0 ∧
    expected.addSummary.numeric = some 1 ∧ left ≠ right := by decide

theorem expected_keeps_marker : expected.addSummary.atoms = {marker.baseClass} ∧
    ¬ BaseEq expected one := by
  refine ⟨by simp [Term.addSummary, AddSummary.combine, AddSummary.number, AddSummary.atom], ?_⟩
  intro h
  have hc := congrArg (fun s => s.atoms.card) h.add_summary
  simp [Term.addSummary, AddSummary.combine, AddSummary.number, AddSummary.atom] at hc

theorem empty_remainder_numeric_output : ModuloStep a one :=
  (RootStep.fst one (.const .bottom)).to_modulo.of_add_summaries .empty (by simp) (by simp)

abbrev expanded : Term Nat := .binary .add (.name 1) (.name 2)
abbrev expanding : Term Nat := .unary .fst (.binary .pair expanded (.const .bottom))

theorem expanding_output_retains_zero :
    AddFactorStep (.binary .add expanding zero) (.binary .add expanded zero) ∧
    (Term.binary .add expanding zero).addSummary.atoms.card = 1 ∧
    (Term.binary .add expanded zero).addSummary.atoms.card = 2 ∧
    (Term.binary .add expanded zero).addSummary.numeric = some 0 :=
  ⟨((RootStep.fst expanded (.const .bottom)).to_modulo.context
    (.binaryLeft .add .hole zero)).add_factor, by decide, by decide, by decide⟩

abbrev bExpandedZero : Term Nat :=
  .unary .snd (.binary .pair (.const .bottom) (.binary .add zero zero))

theorem representative_change_retains_zero :
    AddFactorStep (.binary .add bExpandedZero marker) (.binary .add zero marker) := by
  have he : BaseEq bExpandedZero b :=
    .unary .snd (.binary .pair (.refl _) (.equation .zero_zero))
  exact (((RootStep.snd (.const .bottom) zero).to_modulo.pre_base he).context
    (.binaryLeft .add .hole marker)).add_factor

theorem addition_source_locally_confluent : LocallyConfluentAt source := by
  have ha : LocallyConfluentAt a := locally_confluent_at_unary .fst _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (constant_irreducible .one).locally_confluent_at (constant_irreducible .bottom).locally_confluent_at)
  have hb : LocallyConfluentAt b := locally_confluent_at_unary .snd _
    (locally_confluent_at_passive_binary .pair (Or.inl rfl) _ _
      (constant_irreducible .bottom).locally_confluent_at (constant_irreducible .zero).locally_confluent_at)
  apply locally_confluent_at_of_add_summaries
  apply add_summaries_local_of_representatives
  intro q hq
  simp only [Term.addSummary, AddSummary.combine, AddSummary.atom, AddSummary.number,
    Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero, or_false] at hq
  rcases hq with (rfl | rfl) | rfl
  · exact ⟨a, rfl, ha⟩
  · exact ⟨marker, rfl, (name_irreducible 9).locally_confluent_at⟩
  · exact ⟨b, rfl, hb⟩

end ExplainableCrypto.Helios.Symbolic.AdditionReplacementSPOT
