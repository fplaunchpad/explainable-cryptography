import ExplainableCrypto.Helios.Symbolic.HistoricalValidityExperiments

namespace ExplainableCrypto.Helios.Symbolic.BallotValueExperiments
open ExplainableCrypto.Testing Historical

def bits (n mask : Nat) (j : Fin (n + 1)) : Ground :=
  .const (if mask / 2 ^ j.val % 2 = 0 then .zero else .one)

def vectorCheck (n mask : Nat) : Bool :=
  let xs := (List.finRange (n + 1)).map (bits n mask)
  let count := (xs.filter (· == .const .one)).length
  let summary := (foldCandidates .add (bits n mask)).addSummary
  (summary.atoms.card == 0 && summary.numeric == some count) &&
    ((summary.numeric == some 0 || summary.numeric == some 1) == (count ≤ 1))

def tupleCheck (n mask : Nat) : Bool :=
  let k : Ground := .unary .pk (.name 10)
  let rs := fun j : Fin (n + 1) => Term.name (40 + j.val)
  let cs := fun j => Term.ternary .penc k (rs j) (bits n mask j)
  let ps := fun j => Term.spk k (rs j) (bits n mask j) (cs j)
  let agg := Term.spk k (foldCandidates .compose rs) (foldCandidates .add (bits n mask))
    (foldCandidates .mul cs)
  let fields := (List.finRange (n + 1)).map cs ++ (List.finRange (n + 1)).map ps ++ [agg]
  let ballot := Term.tuple fields
  (fields.length == fieldCount n) &&
    (normalizeRaw (ballot.drop (fieldCount n)) == .const .bottom) &&
    ((List.finRange fields.length).all fun j =>
      normalizeRaw (ballot.project j.val) == normalizeRaw fields[j.val]) &&
    (normalizeRaw ((tupleWithTail fields (.name 99)).drop (fieldCount n)) == .name 99)

def bindingCheck (seed : Nat) : Bool :=
  let k : Ground := .unary .pk (.name 10)
  let r : Ground := .name (40 + seed)
  let s : Ground := .name (41 + seed)
  let bit := if seed % 2 = 0 then Constant.zero else .one
  let c := Term.ternary .penc k r (.const bit)
  let d := Term.ternary .penc k s (.const bit)
  let p := Term.spk k r (.const bit) c
  let delayed := Term.unary .fst (.binary .pair p (.const .bottom))
  (normalizeRaw (.ternary .checkspk k c delayed) == .const .ok) &&
    (normalizeRaw (.ternary .checkspk k d delayed) != .const .ok)

def valuesCheck (seed : Nat) : Bool :=
  let n := seed % 5
  (List.range (2 ^ (n + 1))).all (fun mask => vectorCheck n mask && tupleCheck n mask) && bindingCheck seed

#eval campaign "exactly-one strengthening excludes abstention (negative control)"
  (∀ n : Nat, (foldCandidates .add (bits (n % 5) 0)).addSummary.numeric = some 1) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "bit-vector sums and full proof binding" (∀ n : Nat, valuesCheck n = true) seed
  unless (List.range 256).all valuesCheck do
    throw (IO.userError "ballot-value backstop failed")
  IO.println "ballot-value backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.BallotValueExperiments
