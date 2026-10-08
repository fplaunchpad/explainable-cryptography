import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.RawNormalizationExperiments
open ExplainableCrypto.Testing RewriteExperiments

/-- E3 makes the two keys equal, but raw matching cannot use it. -/
def backgroundSource (n : Nat) : Term Nat :=
  .binary .dec (.const .one)
    (.ternary .penc (.unary .pk (.binary .add (.const .zero) (.const .one))) (.name 1) (.name n))

#eval campaign "raw normalization handles E0-only decryption matches (negative control)"
  (∀ n : Nat, normalizeRaw (backgroundSource n) = .name n) 1 true

def normalizationCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 13)
  let c := generatedTerm (n % 4) (n + 29)
  (reductionPairs a b c (.binary .add a b) (.const .one)).all (fun (l, r) =>
    normalizeRaw l == normalizeRaw r &&
    normalizeRaw (wrap (n % 4) c l) == normalizeRaw (wrap (n % 4) c r)) &&
  (normalizeRaw (normalizeRaw a) == normalizeRaw a) &&
  (normalizeRaw (V := Nat) (.binary .dec (.name 0)
    (.ternary .penc (.unary .pk (.name 0)) (.name 1)
      (.unary .fst (.binary .pair (.name n) (.const .one))))) == .name n)

#eval do
  for seed in [1, 7, 42] do
    campaign "raw normalization preserves root/context fixtures and is idempotent"
      (∀ n : Nat, normalizationCheck n = true) seed
  unless (List.range 256).all normalizationCheck do
    throw (IO.userError "raw-normalization deterministic backstop failed")
  IO.println "raw-normalization deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.RawNormalizationExperiments
