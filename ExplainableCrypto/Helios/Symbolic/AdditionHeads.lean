import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem numericAdd_present (a b : Option Nat) (h : a ≠ none ∨ b ≠ none) :
    numericAdd a b ≠ none := by
  cases a <;> cases b <;> simp_all [numericAdd]

private theorem atoms_pos_without_numeric (t : Term V) (hn : t.addSummary.numeric = none) :
    0 < t.addSummary.atoms.card := by
  apply Multiset.card_pos.mpr
  intro hz
  apply t.addSummary_ne_empty
  have he : t.addSummary = AddSummary.mk 0 none := by
    cases hs : t.addSummary with
    | mk atoms numeric => simp_all
  exact he

/-- An arithmetic sum contains numeric material or at least two nonnumeric atoms.
A present zero remains material; it cannot disappear beside an arbitrary atom. -/
def AdditionEndpoint (t : Term V) : Prop :=
  t.addSummary.numeric ≠ none ∨ 2 ≤ t.addSummary.atoms.card

theorem AdditionEndpoint.add (a b : Term V) : AdditionEndpoint (.binary .add a b) := by
  by_cases ha : a.addSummary.numeric = none
  · by_cases hb : b.addSummary.numeric = none
    · right
      have h₁ := atoms_pos_without_numeric a ha
      have h₂ := atoms_pos_without_numeric b hb
      simp only [Term.addSummary, AddSummary.combine, Multiset.card_add]
      omega
    · left
      exact numericAdd_present _ _ (Or.inr hb)
  · left
    exact numericAdd_present _ _ (Or.inl ha)

theorem AdditionEndpoint.of_base {a b : Term V} (h : AdditionEndpoint a) (he : BaseEq a b) :
    AdditionEndpoint b := by
  unfold AdditionEndpoint at *
  rwa [← he.add_summary]

theorem AdditionEndpoint.step {a b : Term V} (h : AdditionEndpoint a) (hs : ModuloStep a b) :
    AdditionEndpoint b := by
  obtain ⟨x, y, rest, _, _, ha, hb⟩ := hs.add_factor
  unfold AdditionEndpoint at *
  rw [ha] at h
  rw [hb]
  rcases h with hn | hc
  · left
    have hr : rest.numeric ≠ none := by simpa [AddSummary.atom, AddSummary.combine, numericAdd] using hn
    exact numericAdd_present _ _ (Or.inr hr)
  · by_cases hy : y.addSummary.numeric = none
    · right
      have hp := atoms_pos_without_numeric y hy
      simp only [AddSummary.combine, AddSummary.atom, Multiset.card_add, Multiset.card_singleton] at hc ⊢
      omega
    · left
      exact numericAdd_present _ _ (Or.inl hy)

theorem AdditionEndpoint.reduces {a b : Term V} (h : AdditionEndpoint a) (hs : ReducesModulo a b) :
    AdditionEndpoint b := by
  induction hs with
  | base he => exact h.of_base he
  | head hstep _ ih => exact ih (h.step hstep)

theorem AdditionEndpoint.shape {t : Term V} (h : AdditionEndpoint t) :
    (∃ a b, t = .binary .add a b) ∨ t = .const .zero ∨ t = .const .one := by
  cases t with
  | binary f a b => cases f <;> simp_all [AdditionEndpoint, Term.addSummary, AddSummary.atom]
  | const c => cases c <;> simp_all [AdditionEndpoint, Term.addSummary, AddSummary.atom, AddSummary.number]
  | _ => simp_all [AdditionEndpoint, Term.addSummary, AddSummary.atom]

/-- Actual addition paths allow exactly the source's two numeric head collapses. -/
theorem ReducesModulo.add_shape {a b t : Term V} (h : ReducesModulo (.binary .add a b) t) :
    (∃ x y, t = .binary .add x y) ∨ t = .const .zero ∨ t = .const .one :=
  ((AdditionEndpoint.add a b).reduces h).shape

theorem EqE.add_irreducible_shape {a b t : Term V}
    (h : EqE (.binary .add a b) t) (ht : Irreducible t) :
    (∃ x y, t = .binary .add x y) ∨ t = .const .zero ∨ t = .const .one := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  exact (((AdditionEndpoint.add a b).reduces hl).of_base (ht.reducesModulo hr).symm).shape

end ExplainableCrypto.Helios.Symbolic
