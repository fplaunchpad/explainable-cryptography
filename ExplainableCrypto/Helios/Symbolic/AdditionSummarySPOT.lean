import ExplainableCrypto.Helios.Symbolic.AdditionRepresentatives

namespace ExplainableCrypto.Helios.Symbolic.AdditionSummarySPOT

private def zero : Term Nat := .const .zero
private def one : Term Nat := .const .one
private def marker : Term Nat := .name 9
private def mixed : Term Nat := .binary .add (.binary .add marker zero) (.binary .add one one)
private def expected : Term Nat := .binary .add marker (.binary .add one one)

theorem repeated_zero : BaseEq (.binary .add zero zero) zero := .equation .zero_zero

theorem zero_one : BaseEq (.binary .add zero one) one := .equation .zero_one

theorem zero_not_global_identity : ¬ BaseEq (.binary .add marker zero) marker := by
  intro h
  exact AddSummary.atom_zero_not_atom marker.baseClass h.add_summary

theorem repeated_one_not_saturated : ¬ BaseEq (.binary .add one one) one := by
  intro h
  exact AddSummary.two_ones_not_one h.add_summary

theorem mixed_summary : mixed.addSummary = ⟨{marker.baseClass}, some 2⟩ := by
  simp [mixed, marker, zero, one, Term.addSummary, AddSummary.combine,
    AddSummary.atom, AddSummary.number, numericAdd]

theorem mixed_reconstruction : BaseEq mixed expected := by
  apply (baseEq_iff_addSummary _ _).mpr
  rw [mixed_summary]
  simp [expected, marker, one, Term.addSummary, AddSummary.combine,
    AddSummary.atom, AddSummary.number, numericAdd]

theorem mixed_not_single_one : ¬ BaseEq mixed (.binary .add marker one) := by
  intro h
  have hn := congrArg AddSummary.numeric h.add_summary
  rw [mixed_summary] at hn
  simp [marker, one, Term.addSummary, AddSummary.combine,
    AddSummary.atom, AddSummary.number, numericAdd] at hn

theorem repeated_atom_retained : ¬ BaseEq (.binary .add marker marker) marker := by
  intro h
  have hc := congrArg (fun s => s.atoms.card) h.add_summary
  simp [marker, Term.addSummary, AddSummary.combine, AddSummary.atom] at hc

theorem zero_is_present : zero.addSummary.numeric = some 0 ∧ zero.addSummary ≠ .empty :=
  ⟨rfl, zero.addSummary_ne_empty⟩

theorem numeric_representatives (n : Nat) :
    ∃ t : Term Nat, t.addSummary = ⟨0, some n⟩ :=
  ⟨addNumeral n, addNumeral_summary n⟩

theorem retained_atom_with_present_zero :
    ∃ t : Term Nat, t.addSummary = ⟨{marker.baseClass}, some 0⟩ := by
  apply mixed.add_subsummary_representable
  · rw [mixed_summary]
  · intro h
    have hn := congrArg AddSummary.numeric h
    cases hn

/-- An E0 change inside a non-numeric atom remains available under addition. -/
theorem nested_representative_change :
    BaseEq
      (.binary .add (.unary .pk (.binary .compose marker one)) zero)
      (.binary .add (.unary .pk (.binary .compose one marker)) zero) := by
  apply (baseEq_iff_addSummary _ _).mpr
  exact (BaseEq.binary .add
    (.unary .pk (.equation (.comm .compose trivial marker one))) (.refl zero)).add_summary

theorem multiplication_instance_unchanged (a b : Term Nat) :
    a.baseClass * b.baseClass = (Term.binary .mul a b).baseClass := rfl

end ExplainableCrypto.Helios.Symbolic.AdditionSummarySPOT
