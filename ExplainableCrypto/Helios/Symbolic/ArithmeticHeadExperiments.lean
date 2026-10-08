import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.AdditionSummary
import ExplainableCrypto.Helios.Symbolic.ComposeFactors

namespace ExplainableCrypto.Helios.Symbolic.ArithmeticHeadExperiments
open ExplainableCrypto.Testing RewriteExperiments

def sumEndpoint (t : Term Nat) : Bool :=
  t.addSummary.numeric.isSome || (2 ≤ t.addSummary.atoms.card)

def arithmeticCheck (seed : Nat) : Bool :=
  let a := generatedTerm (seed % 4) seed
  let b := generatedTerm (seed % 4) (seed + 13)
  let pairs := reductionPairs a b (.name 3) (.binary .compose a b) (.const .one)
  pairs.all (fun (l, r) =>
    (l.composeFactors.card ≤ r.composeFactors.card) &&
    (sumEndpoint (.binary .add l a)) && (sumEndpoint (.binary .add r a)) &&
    (2 ≤ (Term.binary .compose r a).composeFactors.card)) &&
  (backgroundPairs a b (.name 5)).all (fun (l, r) =>
    (l.composeFactors.card == r.composeFactors.card) &&
    (sumEndpoint l == sumEndpoint r))

#eval campaign "E0 zero+zero endpoint retains its addition head (negative control)"
  (∀ n : Nat, (match (Term.const .zero : Term Nat) with | .binary .add _ _ => true | _ => false) = true ∧ n = n) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "arithmetic endpoint summaries and composition factor counts"
      (∀ n : Nat, arithmeticCheck n = true) seed
  unless (List.range 256).all arithmeticCheck do
    throw (IO.userError "arithmetic head backstop failed")
  IO.println "arithmetic head backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ArithmeticHeadExperiments
