import ExplainableCrypto.Helios.Symbolic.AddSummary
import ExplainableCrypto.Helios.Symbolic.FactorReconstruction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Zero/one summands use optional counts. All other outer factors retain exact
E0 classes. Absence and a present zero are distinct. -/
def Term.addSummary : Term V → AddSummary (BaseClass V)
  | .const .zero => .number 0
  | .const .one => .number 1
  | .binary .add a b => a.addSummary.combine b.addSummary
  | t => .atom t.baseClass

theorem BaseEquation.add_summary {a b : Term V} (h : BaseEquation a b) : a.addSummary = b.addSummary := by
  cases h with
  | zero_one => simp [Term.addSummary]
  | zero_zero => simp [Term.addSummary]
  | comm f hf a b =>
    cases f <;> first
      | exact AddSummary.combine_comm a.addSummary b.addSummary
      | exact congrArg AddSummary.atom (Quotient.sound (.equation (.comm _ hf a b)))
  | assoc f hf a b c =>
    cases f <;> first
      | exact AddSummary.combine_assoc a.addSummary b.addSummary c.addSummary
      | exact congrArg AddSummary.atom (Quotient.sound (.equation (.assoc _ hf a b c)))

theorem BaseEq.add_summary {a b : Term V} (h : BaseEq a b) : a.addSummary = b.addSummary := by
  induction h with
  | equation h => exact h.add_summary
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f h => exact congrArg AddSummary.atom (Quotient.sound (.unary f h))
  | binary f ha hb ih₁ ih₂ =>
    cases f <;> first
      | exact congrArg₂ AddSummary.combine ih₁ ih₂
      | exact congrArg AddSummary.atom (Quotient.sound (.binary _ ha hb))
  | ternary f ha hb hc => exact congrArg AddSummary.atom (Quotient.sound (.ternary f ha hb hc))
  | spk ha hb hc hd => exact congrArg AddSummary.atom (Quotient.sound (.spk ha hb hc hd))

/-- A representative of a present numeric count. The leading zero is harmless
only in this numeric family; it is not an identity for arbitrary terms. -/
def addNumeral : Nat → Term V
  | 0 => .const .zero
  | n + 1 => .binary .add (addNumeral n) (.const .one)

theorem addNumeral_add_zero (n : Nat) :
    BaseEq (.binary .add (addNumeral (V := V) n) (.const .zero)) (addNumeral n) := by
  cases n with
  | zero => exact .equation .zero_zero
  | succ n =>
    exact (BaseEq.equation (.assoc .add trivial (addNumeral n) (.const .one) (.const .zero))).trans
      (.binary .add (.refl _) ((BaseEq.equation (.comm .add trivial (.const .one) (.const .zero))).trans
        (.equation .zero_one)))

theorem addNumerals_combine (n m : Nat) :
    BaseEq (.binary .add (addNumeral (V := V) n) (addNumeral m)) (addNumeral (n + m)) := by
  induction m with
  | zero => exact addNumeral_add_zero n
  | succ m ih =>
    exact (BaseEq.equation (.assoc .add trivial (addNumeral n) (addNumeral m) (.const .one))).symm.trans
      (.binary .add ih (.refl _))

theorem addNumeral_summary (n : Nat) : (addNumeral (V := V) n).addSummary = .number n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [addNumeral, Term.addSummary, ih, AddSummary.combine_numbers]

end ExplainableCrypto.Helios.Symbolic
