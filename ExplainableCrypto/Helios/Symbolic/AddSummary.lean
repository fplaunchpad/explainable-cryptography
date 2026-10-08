import Mathlib.Data.Multiset.AddSub

namespace ExplainableCrypto.Helios.Symbolic

/-- Absence is a bookkeeping identity; a present zero remains a real summand. -/
def numericAdd : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (a + b)

/-- Generic summary algebra. Concrete term summaries use exact E0 classes as atoms. -/
structure AddSummary (α : Type) where
  atoms : Multiset α
  numeric : Option Nat
  deriving DecidableEq

theorem numericAdd_comm (a b : Option Nat) : numericAdd a b = numericAdd b a := by
  cases a <;> cases b <;> simp [numericAdd, Nat.add_comm]

theorem numericAdd_assoc (a b c : Option Nat) :
    numericAdd (numericAdd a b) c = numericAdd a (numericAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [numericAdd, Nat.add_assoc]

namespace AddSummary
variable {α : Type}

def empty : AddSummary α := ⟨0, none⟩
def atom (a : α) : AddSummary α := ⟨{a}, none⟩
def number (n : Nat) : AddSummary α := ⟨0, some n⟩
def combine (a b : AddSummary α) : AddSummary α :=
  ⟨a.atoms + b.atoms, numericAdd a.numeric b.numeric⟩

theorem combine_comm (a b : AddSummary α) : a.combine b = b.combine a := by
  cases a; cases b
  simp [combine, Multiset.add_comm, numericAdd_comm]

theorem combine_assoc (a b c : AddSummary α) : (a.combine b).combine c = a.combine (b.combine c) := by
  cases a; cases b; cases c
  simp [combine, Multiset.add_assoc, numericAdd_assoc]

@[simp] theorem combine_empty (a : AddSummary α) : a.combine empty = a := by
  cases a with
  | mk atoms numeric => cases numeric <;> simp [combine, empty, numericAdd]

@[simp] theorem empty_combine (a : AddSummary α) : empty.combine a = a := by
  rw [combine_comm, combine_empty]

@[simp] theorem combine_numbers (n m : Nat) :
    (number n : AddSummary α).combine (number m) = number (n + m) := by
  simp [combine, number, numericAdd]

/-- The two failed candidate simplifications are rejected by numeric presence/count. -/
theorem atom_zero_not_atom (a : α) : (atom a).combine (number 0) ≠ atom a := by
  intro h
  have hn := congrArg AddSummary.numeric h
  cases hn

theorem two_ones_not_one : (number 1 : AddSummary α).combine (number 1) ≠ number 1 := by
  intro h
  have hn := congrArg AddSummary.numeric h
  simp [combine, number, numericAdd] at hn

end AddSummary
end ExplainableCrypto.Helios.Symbolic
