import ExplainableCrypto.Helios.Symbolic.ComposeFactorExperiments
import ExplainableCrypto.Helios.Symbolic.RawNormalization

namespace ExplainableCrypto.Helios.Symbolic.ComposedNonceExperiments
open ExplainableCrypto.Testing RewriteExperiments ComposeFactorExperiments

def composedCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) (n + 7)
  let b := generatedTerm (n % 4) (n + 13)
  let expanded := Term.binary .compose (.name (n + 1)) (.name (n + 2))
  let p := Term.unary .fst (.binary .pair expanded (.const .bottom))
  let t := Term.binary .compose (.binary .compose (.name n) a)
    (.binary .compose p (.binary .compose b (.name n)))
  decide (2 ≤ (rawFactors t).count (.name n) ∧
    (rawFactors t).count (.name n) ≤ (rawFactors (normalizeRaw t)).count (.name n))

#eval campaign "arbitrary syntactic name occurrences persist (negative control)"
  (∀ n : Nat, normalizeRaw (Term.unary .fst (.binary .pair (.const .one) (.name n)) : Term Nat) ≠ .const .one) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "outer composition name factors survive normalization"
      (∀ n : Nat, composedCheck n = true) seed
  unless (List.range 256).all composedCheck do
    throw (IO.userError "composed nonce backstop failed")
  IO.println "composed nonce backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ComposedNonceExperiments
