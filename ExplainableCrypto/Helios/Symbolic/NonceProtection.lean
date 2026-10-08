import ExplainableCrypto.Helios.Symbolic.Terms

namespace ExplainableCrypto.Helios.Symbolic

/-- Protected names may occur under pk/spk or in encryption randomness. Plaintext
and every argument with an exposing destructor remain checked. This is metatheory. -/
def Term.nonceSafe {V : Type} (restricted : Finset Nat) : Term V → Bool
  | .name n => decide (n ∉ restricted)
  | .var _ | .const _ => true
  | .unary .pk _ => true
  | .unary _ a => a.nonceSafe restricted
  | .binary _ a b => a.nonceSafe restricted && b.nonceSafe restricted
  | .ternary .penc k _ m => k.nonceSafe restricted && m.nonceSafe restricted
  | .ternary .checkspk a b c => a.nonceSafe restricted && b.nonceSafe restricted && c.nonceSafe restricted
  | .spk _ _ _ _ => true

end ExplainableCrypto.Helios.Symbolic
