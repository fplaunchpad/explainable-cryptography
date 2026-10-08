import ExplainableCrypto.Helios.Symbolic.AdditionSummary

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

section AdditionFold

/-- The fold uses addition only in this section; exported quotient multiplication
continues to denote multiplication. -/
local instance additionSemigroup : CommSemigroup (BaseClass V) where
  mul a b := Quotient.liftOn₂ a b (fun a b => (Term.binary .add a b).baseClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := baseSetoid V) (.binary .add ha hb))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := baseSetoid V) (.equation (.assoc .add trivial a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := baseSetoid V) (.equation (.comm .add trivial a b))

private def numericProduct : Option Nat → WithOne (BaseClass V)
  | none => 1
  | some n => ((addNumeral (V := V) n).baseClass : WithOne (BaseClass V))

private theorem numericProduct_combine (a b : Option Nat) :
    numericProduct (V := V) (numericAdd a b) = numericProduct a * numericProduct b := by
  cases a with
  | none => cases b <;> simp [numericAdd, numericProduct]
  | some n =>
    cases b with
    | none => simp [numericAdd, numericProduct]
    | some m =>
      exact congrArg (fun q : BaseClass V => (q : WithOne (BaseClass V)))
        ((baseClass_eq_iff _ _).mpr (addNumerals_combine n m)).symm

private def summaryProduct (s : AddSummary (BaseClass V)) : WithOne (BaseClass V) :=
  (s.atoms.map fun q : BaseClass V => (q : WithOne (BaseClass V))).prod * numericProduct s.numeric

private theorem summaryProduct_combine (a b : AddSummary (BaseClass V)) :
    summaryProduct (a.combine b) = summaryProduct a * summaryProduct b := by
  simp only [summaryProduct, AddSummary.combine, Multiset.map_add, Multiset.prod_add, numericProduct_combine]
  ac_rfl

private theorem summaryProduct_atom (q : BaseClass V) :
    summaryProduct (.atom q) = (q : WithOne (BaseClass V)) := by
  simp [summaryProduct, AddSummary.atom, numericProduct]

private theorem summaryProduct_number (n : Nat) :
    summaryProduct (V := V) (.number n) = ((addNumeral (V := V) n).baseClass : WithOne (BaseClass V)) := by
  simp [summaryProduct, AddSummary.number, numericProduct]

private theorem addSummary_reconstruct (t : Term V) :
    summaryProduct t.addSummary = (t.baseClass : WithOne (BaseClass V)) := by
  induction t with
  | name => exact summaryProduct_atom _
  | var => exact summaryProduct_atom _
  | const c =>
    cases c with
    | zero => exact summaryProduct_number 0
    | one =>
      exact (summaryProduct_number 1).trans
        (congrArg (fun q : BaseClass V => (q : WithOne (BaseClass V)))
          ((baseClass_eq_iff _ _).mpr (.equation .zero_one)))
    | ok => exact summaryProduct_atom _
    | bottom => exact summaryProduct_atom _
  | unary => exact summaryProduct_atom _
  | binary f a b ha hb =>
    cases f <;> first
      | exact (by rw [Term.addSummary, summaryProduct_combine, ha, hb]; rfl)
      | exact summaryProduct_atom _
  | ternary => exact summaryProduct_atom _
  | spk => exact summaryProduct_atom _

/-- Exact completeness for summaries of actual terms. Arbitrary abstract
summaries need not have well-formed non-numeric atom representatives. -/
theorem baseEq_iff_addSummary (a b : Term V) : BaseEq a b ↔ a.addSummary = b.addSummary := by
  refine ⟨BaseEq.add_summary, ?_⟩
  intro he
  have hp := congrArg summaryProduct he
  rw [addSummary_reconstruct a, addSummary_reconstruct b] at hp
  exact (baseClass_eq_iff _ _).mp (WithOne.coe_injective hp)

/-- Empty is only the bookkeeping identity; even a literal zero has a numeric part. -/
theorem Term.addSummary_ne_empty (t : Term V) : t.addSummary ≠ .empty := by
  intro he
  have hp := congrArg summaryProduct he
  rw [addSummary_reconstruct t] at hp
  simp [summaryProduct, AddSummary.empty, numericProduct] at hp

end AdditionFold
end ExplainableCrypto.Helios.Symbolic
