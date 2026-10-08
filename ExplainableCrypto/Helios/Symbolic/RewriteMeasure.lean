import ExplainableCrypto.Helios.Symbolic.Equations

namespace ExplainableCrypto.Helios.Symbolic

/-- Counts non-AC structure; E3/E4 and the background AC equations preserve it. -/
def Term.cryptoWeight {V : Type} : Term V → Nat
  | .name _ | .var _ => 1
  | .const _ => 0
  | .unary _ a => 1 + a.cryptoWeight
  | .binary f a b => (match f with | .mul | .add | .compose => 0 | _ => 1) +
      a.cryptoWeight + b.cryptoWeight
  | .ternary _ a b c => 1 + a.cryptoWeight + b.cryptoWeight + c.cryptoWeight
  | .spk a b c d => 1 + a.cryptoWeight + b.cryptoWeight + c.cryptoWeight + d.cryptoWeight

/-- Syntax size is useful as a deliberately wrong background-invariant control. -/
def Term.nodeCount {V : Type} : Term V → Nat
  | .name _ | .var _ | .const _ => 1
  | .unary _ a => 1 + a.nodeCount
  | .binary _ a b => 1 + a.nodeCount + b.nodeCount
  | .ternary _ a b c => 1 + a.nodeCount + b.nodeCount + c.nodeCount
  | .spk a b c d => 1 + a.nodeCount + b.nodeCount + c.nodeCount + d.nodeCount

end ExplainableCrypto.Helios.Symbolic
