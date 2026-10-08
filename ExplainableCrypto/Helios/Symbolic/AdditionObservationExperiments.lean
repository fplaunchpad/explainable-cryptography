import ExplainableCrypto.Helios.Symbolic.CompositionObservationExperiments
import ExplainableCrypto.Helios.Symbolic.AddSummary

namespace ExplainableCrypto.Helios.Symbolic.AdditionObservationExperiments
open ExplainableCrypto.Testing

private def reveal (t : Ground) := Term.unary .fst (.binary .pair t (.const .bottom))
private def atom (seed : Nat) : Ground :=
  let x := Term.name (40 + seed / 4 % 4)
  match seed % 4 with
  | 0 => x | 1 => .unary .pk x | 2 => .binary .pair x (.name 50) | _ => .unary .fst x

/-- Executable proxy: normalize each retained raw atom; preserve numeric presence. -/
private def summary : Ground → AddSummary Ground
  | .const .zero => .number 0
  | .const .one => .number 1
  | .binary .add a b => (summary a).combine (summary b)
  | t => .atom (normalizeRaw t)

private def numeral : Nat → Ground
  | 0 => .const .zero
  | n+1 => .binary .add (numeral n) (.const .one)

def summaryCheck (seed : Nat) : Bool :=
  let a := atom seed
  let b := atom (seed / 16)
  let n := seed / 256 % 5
  let x := Term.binary .add (reveal a)
    (.binary .add (numeral n) (.binary .add (reveal b) (reveal a)))
  let y := Term.binary .add (.binary .add a a) (.binary .add b (numeral n))
  let expected : AddSummary Ground := ⟨{a,b,a}, some n⟩
  decide (summary x = expected) && decide (summary y = expected) &&
    decide (summary (normalizeRaw x) = expected) &&
    decide (summary (.binary .add a (.const .zero)) ≠ summary a) &&
    decide (summary (.binary .add (.const .one) (.const .one)) ≠ summary (.const .one)) &&
    decide (summary (.binary .add a a) ≠ summary a)

def hiddenSum (seed : Nat) : Bool :=
  let t : Ground := if seed % 2 = 0 then .const .zero else .binary .add (.name 40) (.name 41)
  decide (summary (reveal t) = summary (normalizeRaw (reveal t)))

def erasedZero (_seed : Nat) : Bool :=
  decide (summary (.binary .add (.name 40) (.const .zero)) = summary (.name 40))

#eval campaign "addition hidden numeric/additive value (negative control)" (∀ n : Nat, hiddenSum n = true) 1 true
#eval campaign "addition deleted numeric presence (negative control)" (∀ n : Nat, erasedZero n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "full-E addition proxy retains atom counts and numeric presence" (∀ n : Nat, summaryCheck n = true) seed
  unless (List.range 5120).all summaryCheck do
    throw (IO.userError "addition observation backstop failed")
  IO.println "addition observation backstop: 5120 inputs passed"

end ExplainableCrypto.Helios.Symbolic.AdditionObservationExperiments
