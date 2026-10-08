import ExplainableCrypto.Helios.Symbolic.AdditionReconstruction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem add_singleton_representable (t : Term V)
    (ht : t.addSummary = .atom t.baseClass) {q : BaseClass V}
    (h : q ∈ t.addSummary.atoms) : ∃ a : Term V, a.addSummary = .atom q := by
  rw [ht, AddSummary.atom, Multiset.mem_singleton] at h
  exact ⟨t, h ▸ ht⟩

theorem Term.add_atom_representable (t : Term V) {q : BaseClass V}
    (h : q ∈ t.addSummary.atoms) : ∃ a : Term V, a.addSummary = .atom q := by
  induction t with
  | binary f a b ha hb =>
    by_cases hf : f = .add
    · subst f
      rcases Multiset.mem_add.mp h with h | h
      · exact ha h
      · exact hb h
    · exact add_singleton_representable (.binary f a b)
        (by cases f <;> simp_all [Term.addSummary]) h
  | const c =>
    cases c <;> first
      | exact add_singleton_representable _ rfl h
      | simp [Term.addSummary, AddSummary.number] at h
  | name n => exact add_singleton_representable (.name n) rfl h
  | var v => exact add_singleton_representable (.var v) rfl h
  | unary f a _ => exact add_singleton_representable (.unary f a) rfl h
  | ternary f a b c _ _ _ => exact add_singleton_representable (.ternary f a b c) rfl h
  | spk a b c d _ _ _ _ => exact add_singleton_representable (.spk a b c d) rfl h

theorem add_atoms_representable (s : Multiset (BaseClass V)) (hne : s ≠ 0)
    (hrep : ∀ q ∈ s, ∃ a : Term V, a.addSummary = .atom q) :
    ∃ a : Term V, a.addSummary = ⟨s, none⟩ := by
  induction s using Multiset.induction_on with
  | empty => exact False.elim (hne rfl)
  | cons q s ih =>
    obtain ⟨a, ha⟩ := hrep q (by simp)
    by_cases hs : s = 0
    · subst s
      exact ⟨a, by simpa [AddSummary.atom] using ha⟩
    · obtain ⟨b, hb⟩ := ih hs (fun r hr => hrep r (by simp [hr]))
      refine ⟨.binary .add a b, ?_⟩
      simp only [Term.addSummary, ha, hb, AddSummary.atom, AddSummary.combine,
        numericAdd, Multiset.singleton_add]

/-- Numeric counts are freely representable; the atom premise excludes invalid
abstract atoms such as the E0 class of zero used as a non-numeric factor. -/
theorem add_summary_representable (s : AddSummary (BaseClass V)) (hne : s ≠ .empty)
    (hrep : ∀ q ∈ s.atoms, ∃ a : Term V, a.addSummary = .atom q) :
    ∃ a : Term V, a.addSummary = s := by
  rcases s with ⟨atoms, numeric⟩
  cases numeric with
  | none =>
    exact add_atoms_representable atoms (fun h => hne (by cases h; rfl)) hrep
  | some n =>
    by_cases hs : atoms = 0
    · subst atoms
      exact ⟨addNumeral n, addNumeral_summary n⟩
    · obtain ⟨a, ha⟩ := add_atoms_representable atoms hs hrep
      refine ⟨.binary .add a (addNumeral n), ?_⟩
      simp [Term.addSummary, ha, addNumeral_summary, AddSummary.combine,
        AddSummary.number, numericAdd]

theorem Term.add_subsummary_representable (t : Term V) (s : AddSummary (BaseClass V))
    (hs : s.atoms ≤ t.addSummary.atoms) (hne : s ≠ .empty) :
    ∃ a : Term V, a.addSummary = s :=
  add_summary_representable s hne
    (fun _ h => t.add_atom_representable (Multiset.mem_of_le hs h))

end ExplainableCrypto.Helios.Symbolic
