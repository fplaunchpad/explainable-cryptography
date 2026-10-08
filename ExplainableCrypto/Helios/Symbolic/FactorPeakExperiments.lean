import ExplainableCrypto.Testing.Plausible
import ExplainableCrypto.Helios.Symbolic.RewriteMeasure
import Mathlib.Data.Multiset.AddSub

namespace ExplainableCrypto.Helios.Symbolic.FactorPeakExperiments
open ExplainableCrypto.Testing

#eval campaign "every selected factor has strictly smaller crypto weight (negative control)"
  (∀ n : Nat, (Term.name n : Term Nat).cryptoWeight <
    (Term.binary .mul (.name n) (.const .zero) : Term Nat).cryptoWeight) 1 true

/-- Valid source occurrences; outputs deliberately expand to two-element bags.
Repeated values need not identify unique syntax positions. -/
def factorCheck (n : Nat) : Bool :=
  let len := 2 + n % 7
  let xs := (List.range len).map (fun i => (n / (i + 1) + i) % 4)
  let source : Multiset Nat := xs
  let x := xs[n % len]!
  let y := xs[(n / 11) % len]!
  let rx := source - {x}
  let ry := source - {y}
  let rest := source - {x, y}
  let outx : Multiset Nat := {n, n + 1}
  let outy : Multiset Nat := {n + 2, n + 3}
  decide (source = {x} + rx ∧ source = {y} + ry ∧
    ((x = y ∧ rx = ry) ∨
      (rx = {y} + rest ∧ ry = {x} + rest ∧
       outx + rx = {y} + (outx + rest) ∧
       outy + ry = {x} + (outy + rest) ∧
       outy + (outx + rest) = outx + (outy + rest))))

#eval do
  for seed in [1, 7, 42] do
    campaign "singleton selections decompose and disjoint replacement bags commute"
      (∀ n : Nat, factorCheck n = true) seed
  unless (List.range 256).all factorCheck do
    throw (IO.userError "factor-peak deterministic backstop failed")
  IO.println "factor-peak deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.FactorPeakExperiments
