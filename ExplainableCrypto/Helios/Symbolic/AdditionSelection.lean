import ExplainableCrypto.Helios.Symbolic.AdditionReduction
import ExplainableCrypto.Helios.Symbolic.FactorPeak

namespace ExplainableCrypto.Helios.Symbolic.AddSummary
variable {α : Type}

theorem eq_of_fields {a b : AddSummary α} (ha : a.atoms = b.atoms)
    (hn : a.numeric = b.numeric) : a = b := by
  cases a; cases b; cases ha; cases hn; rfl

/-- Cancellation applies to a non-numeric atom, not to arbitrary numeric parts. -/
theorem atom_selection_cases (source : AddSummary α) (x y : α)
    (rx ry : AddSummary α) (hx : source = (atom x).combine rx)
    (hy : source = (atom y).combine ry) :
    (x = y ∧ rx = ry) ∨ ∃ rest, rx = (atom y).combine rest ∧ ry = (atom x).combine rest := by
  have hnx : source.numeric = rx.numeric := by
    simpa [combine, atom, numericAdd] using congrArg AddSummary.numeric hx
  have hny : source.numeric = ry.numeric := by
    simpa [combine, atom, numericAdd] using congrArg AddSummary.numeric hy
  rcases singleton_selection_cases source.atoms x y rx.atoms ry.atoms
    (congrArg AddSummary.atoms hx) (congrArg AddSummary.atoms hy) with
    ⟨he, hr⟩ | ⟨rest, hrx, hry⟩
  · exact Or.inl ⟨he, eq_of_fields hr (hnx.symm.trans hny)⟩
  · exact Or.inr ⟨⟨rest, source.numeric⟩,
      eq_of_fields hrx hnx.symm, eq_of_fields hry hny.symm⟩

theorem numeric_cancellation_refuted :
    numericAdd (some 1) none = numericAdd (some 1) (some 0) ∧
      (none : Option Nat) ≠ some 0 := by decide

end ExplainableCrypto.Helios.Symbolic.AddSummary
