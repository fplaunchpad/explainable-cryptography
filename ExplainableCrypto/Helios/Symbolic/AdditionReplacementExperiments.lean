import ExplainableCrypto.Helios.Symbolic.AddSummaryExperiments

namespace ExplainableCrypto.Helios.Symbolic.AdditionReplacementExperiments
open ExplainableCrypto.Testing
open AddSummaryExperiments

def replacementCheck (n : Nat) : Bool :=
  let x := AddSummary.atom (n % 4)
  let y := AddSummary.atom ((n + 1) % 4)
  let a := generated (n + 3)
  let b := generated (n + 11)
  let r := generated (n + 19)
  let leftFinal := a.combine (b.combine r)
  let rightFinal := b.combine (a.combine r)
  decide (leftFinal = rightFinal ∧
    x.combine (y.combine r) = y.combine (x.combine r) ∧
    (x.combine a = x.combine b ↔ a = b) ∧
    (x.combine r).numeric = r.numeric)

#eval campaign "numeric cancellation is valid (negative control)"
  (∀ n : Nat, numericAdd (some (n + 1)) none ≠ numericAdd (some (n + 1)) (some 0)) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "addition atom cancellation and disjoint output replacement"
      (∀ n : Nat, replacementCheck n = true) seed
  unless (List.range 256).all replacementCheck do
    throw (IO.userError "addition replacement deterministic backstop failed")
  IO.println "addition replacement deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.AdditionReplacementExperiments
