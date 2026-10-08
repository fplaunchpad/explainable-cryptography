import ExplainableCrypto.Helios.Symbolic.Frames
import Mathlib.Data.Nat.Pairing

/-! A separating algebra for E. This is NOT attacker evaluation: its encryption
interpretation exposes the plaintext. Soundness only lets unequal interpretations
refute equational equality, and does not establish completeness or normal forms. -/
namespace ExplainableCrypto.Helios.Symbolic

namespace Term
variable {V : Type}

def interpretUnary : Unary → Nat → Nat
  | .fst, a => (Nat.unpair a).1
  | .snd, a => (Nat.unpair a).2
  | .pk, _ => 0

def interpretBinary : Binary → Nat → Nat → Nat
  | .pair, a, b => Nat.pair a b
  | .mul, a, b | .add, a, b | .compose, a, b => a + b
  | .partialDecrypt, _, _ => 0
  | .dec, _, b => b

def interpretTernary : Ternary → Nat → Nat → Nat → Nat
  | .penc, _, _, c => c
  | .checkspk, _, _, _ => 0

def denote (names : Nat → Nat) (vars : V → Nat) : Term V → Nat
  | .name n => names n
  | .var v => vars v
  | .const .one => 1
  | .const .bottom => 2
  | .const _ => 0
  | .unary f a => interpretUnary f (denote names vars a)
  | .binary f a b => interpretBinary f (denote names vars a) (denote names vars b)
  | .ternary f a b c => interpretTernary f
      (denote names vars a) (denote names vars b) (denote names vars c)
  | .spk _ _ _ _ => 0

end Term

variable {V : Type}

theorem Equation.denote {a b : Term V} (h : Equation a b)
    (names : Nat → Nat) (vars : V → Nat) : a.denote names vars = b.denote names vars := by
  cases h <;> simp only [Term.denote, Term.interpretUnary, Term.interpretBinary,
    Term.interpretTernary, Nat.unpair_pair, Nat.zero_add]
  case comm f h a b => cases f <;> simp_all [AC, Nat.add_comm]
  case assoc f h a b c => cases f <;> simp_all [AC, Nat.add_assoc]

theorem EqE.denote {a b : Term V} (h : EqE a b)
    (names : Nat → Nat) (vars : V → Nat) : a.denote names vars = b.denote names vars := by
  induction h with
  | equation h => exact h.denote names vars
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f _ ih => exact congrArg (Term.interpretUnary f) ih
  | binary f _ _ ih₁ ih₂ => simp only [Term.denote, ih₁, ih₂]
  | ternary f _ _ _ ih₁ ih₂ ih₃ => simp only [Term.denote, ih₁, ih₂, ih₃]
  | spk => rfl

theorem zero_not_one : ¬ EqE (V := V) (.const .zero) (.const .one) := by
  intro h
  have := h.denote (fun _ => 0) (fun _ => 0)
  simp [Term.denote] at this

theorem two_not_one : ¬ EqE (V := V)
    (.binary .add (.const .one) (.const .one)) (.const .one) := by
  intro h
  have := h.denote (fun _ => 0) (fun _ => 0)
  simp [Term.denote, Term.interpretBinary] at this

end ExplainableCrypto.Helios.Symbolic
