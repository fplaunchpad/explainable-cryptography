import Mathlib.Data.Finset.Basic

/-! The fixed-arity signature in Cortier–Smyth §5.2.1, including `pk` from E5/E6.
Names and variables are separate. There are no destructors for encryption or proofs
other than those explicitly present in the source theory. -/
namespace ExplainableCrypto.Helios.Symbolic

inductive Constant | ok | zero | one | bottom deriving DecidableEq, Repr
inductive Unary | fst | snd | pk deriving DecidableEq, Repr
inductive Binary | pair | mul | add | compose | partialDecrypt | dec deriving DecidableEq, Repr
inductive Ternary | penc | checkspk deriving DecidableEq, Repr

inductive Term (V : Type) where
  | name : Nat → Term V
  | var : V → Term V
  | const : Constant → Term V
  | unary : Unary → Term V → Term V
  | binary : Binary → Term V → Term V → Term V
  | ternary : Ternary → Term V → Term V → Term V → Term V
  | spk : Term V → Term V → Term V → Term V → Term V
  deriving DecidableEq, Repr

namespace Term
variable {V W U : Type}

def subst (σ : V → Term W) : Term V → Term W
  | .name n => .name n
  | .var v => σ v
  | .const c => .const c
  | .unary f a => .unary f (subst σ a)
  | .binary f a b => .binary f (subst σ a) (subst σ b)
  | .ternary f a b c => .ternary f (subst σ a) (subst σ b) (subst σ c)
  | .spk a b c d => .spk (subst σ a) (subst σ b) (subst σ c) (subst σ d)

@[simp] theorem subst_var (t : Term V) : subst .var t = t := by
  induction t <;> simp_all [subst]

@[simp] theorem subst_subst (σ : V → Term W) (τ : W → Term U) (t : Term V) :
    subst τ (subst σ t) = subst (fun v => subst τ (σ v)) t := by
  induction t <;> simp_all [subst]

/-- A recipe may use public names, but must not name restricted atoms. -/
def Public (restricted : Finset Nat) : Term V → Prop
  | .name n => n ∉ restricted
  | .var _ | .const _ => True
  | .unary _ a => Public restricted a
  | .binary _ a b => Public restricted a ∧ Public restricted b
  | .ternary _ a b c => Public restricted a ∧ Public restricted b ∧ Public restricted c
  | .spk a b c d => Public restricted a ∧ Public restricted b ∧
      Public restricted c ∧ Public restricted d

end Term

abbrev Ground := Term Empty
abbrev Recipe (n : Nat) := Term (Fin n)

end ExplainableCrypto.Helios.Symbolic
