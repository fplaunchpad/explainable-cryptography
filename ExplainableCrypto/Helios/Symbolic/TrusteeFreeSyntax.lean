import ExplainableCrypto.Helios.Symbolic.ResultHandleTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Every partial-decryption subterm has a key distinct from the designated
secret under full E. All arguments are inspected, including opaque positions.
This is metatheory and adds no equation or protocol observation. -/
def Term.TrusteeFree (secret : Nat) : Term V → Prop
  | .name _ | .var _ | .const _ => True
  | .unary _ a => a.TrusteeFree secret
  | .binary f a b => a.TrusteeFree secret ∧ b.TrusteeFree secret ∧
      (f = .partialDecrypt → ¬ EqE a (.name secret))
  | .ternary _ a b c => a.TrusteeFree secret ∧ b.TrusteeFree secret ∧ c.TrusteeFree secret
  | .spk a b c d => a.TrusteeFree secret ∧ b.TrusteeFree secret ∧ c.TrusteeFree secret ∧ d.TrusteeFree secret

/-- Some E-equal representative has no partial keyed by the designated secret.
Raw terms with erasable forbidden subterms can still satisfy this value property. -/
def TrusteeFreeValue (secret : Nat) (t : Term V) : Prop :=
  ∃ u, EqE t u ∧ u.TrusteeFree secret

end ExplainableCrypto.Helios.Symbolic
