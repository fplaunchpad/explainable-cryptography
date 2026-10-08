import ExplainableCrypto.Helios.Symbolic.HistoricalSelectorExperiments

namespace ExplainableCrypto.Helios.Symbolic.CiphertextProductExperiments
open ExplainableCrypto.Testing Historical

abbrev ns := HistoricalFrameSPOT.names
abbrev fr := frame ns false 0 1

/-- Ciphertext recipe, independently assembled public plaintext recipe, nonce value. -/
def sample : Nat → Nat → Recipe 3 × Recipe 3 × Ground
  | 0, seed =>
    if seed % 2 = 0 then
      let r : Recipe 3 := .name (40 + seed)
      let m : Recipe 3 := .binary .add (.const .one) (.name (70 + seed))
      (.ternary .penc (.var 0) r m, m, .name (40 + seed))
    else
      let voter := (seed / 2) % 2
      let field := (seed / 4) % 2
      ((Term.var (if voter = 0 then 1 else 2)).project field,
        .const (if voter = field then .one else .zero), .name (20 + 2 * voter + field))
  | depth + 1, seed =>
    let (a, p, r) := sample depth (seed / 2)
    let (b, q, s) := sample depth (seed / 3 + 7)
    (.binary .mul a b, .binary .add p q, .binary .compose r s)

def productCheck (seed : Nat) : Bool :=
  let (c, m, r) := sample (seed % 4) seed
  (normalizeRaw (fr.eval c) ==
    .ternary .penc (publicKey ns) (normalizeRaw r) (normalizeRaw (fr.eval m))) &&
    (m.nodeCount < c.nodeCount)

#eval campaign "duplicate honest ciphertext product returns only one vote (negative control)"
  (∀ n : Nat,
    let c : Recipe 3 := (Term.var 1).project 0
    let doubled := normalizeRaw (fr.eval (.binary .mul c c))
    doubled = .ternary .penc (publicKey ns)
      (.binary .compose (.name 20) (.name 20)) (.const .one) ∧ n = n) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "mixed ciphertext products preserve message trees and shrink plaintext recipes"
      (∀ n : Nat, productCheck n = true) seed
  unless (List.range 256).all productCheck do
    throw (IO.userError "ciphertext product backstop failed")
  IO.println "ciphertext product backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.CiphertextProductExperiments
