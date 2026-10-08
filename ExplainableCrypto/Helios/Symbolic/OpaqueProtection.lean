import ExplainableCrypto.Helios.Symbolic.NonceProtection
import ExplainableCrypto.Helios.Symbolic.Equations

namespace ExplainableCrypto.Helios.Symbolic

/-- Name protection for frames publishing partials. There is no destructor for
pk, spk or either partialDecrypt field. Ciphertext plaintexts remain checked,
since decryption can expose them. This predicate does not change the theory. -/
def Term.opaqueSafe {V : Type} (restricted : Finset Nat) : Term V → Bool
  | .name n => decide (n ∉ restricted)
  | .var _ | .const _ => true
  | .unary .pk _ => true
  | .unary _ a => a.opaqueSafe restricted
  | .binary .partialDecrypt _ _ => true
  | .binary _ a b => a.opaqueSafe restricted && b.opaqueSafe restricted
  | .ternary .penc k _ m => k.opaqueSafe restricted && m.opaqueSafe restricted
  | .ternary .checkspk a b c => a.opaqueSafe restricted && b.opaqueSafe restricted && c.opaqueSafe restricted
  | .spk _ _ _ _ => true

/-- Some E-equal representative protects the names. Raw syntax itself may
contain irrelevant restricted-name occurrences under reducible contexts. -/
def OpaqueProtectedValue {V : Type} (restricted : Finset Nat) (t : Term V) : Prop :=
  ∃ u, EqE t u ∧ u.opaqueSafe restricted = true

end ExplainableCrypto.Helios.Symbolic
