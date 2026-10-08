import ExplainableCrypto.Helios.Symbolic.BallotValueExperiments

namespace ExplainableCrypto.Helios.Symbolic.CandidateSubstitutionExperiments
open ExplainableCrypto.Testing Historical BallotValueExperiments

def represented (seed : Nat) (bit : Ground) : Ground :=
  match seed % 4 with
  | 0 => bit
  | 1 => .unary .fst (.binary .pair bit (.const .bottom))
  | 2 => .binary .dec (.name 90) (.ternary .penc (.unary .pk (.name 90)) (.name 91) bit)
  | _ => .binary .add (.const .zero) bit

def candidateCheck (seed : Nat) : Bool :=
  let n := seed % 5
  (List.range (2 ^ (n + 1))).all fun mask =>
    let raw := fun j => represented (seed + j.val) (bits n mask j)
    let source := foldCandidates .add raw
    let normal := normalizeRaw source
    let count := ((List.finRange (n + 1)).filter (fun j => mask / 2 ^ j.val % 2 = 1)).length
    let summary := normal.addSummary
    (summary.atoms.card == 0) && (summary.numeric == some count) &&
      ((summary.numeric == some 0 || summary.numeric == some 1) == (count ≤ 1)) &&
      ((List.finRange (n + 1)).all fun j =>
        let s := (normalizeRaw (raw j)).addSummary
        s.atoms.card == 0 && s.numeric == some (if mask / 2 ^ j.val % 2 = 0 then 0 else 1))

#eval campaign "zero numeric interpretation implies a candidate sum (negative control)"
  (∀ n : Nat, (foldCandidates (n := n % 5) .add (fun _ => (Term.const .ok : Ground))).addSummary.numeric = some 0)
  1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "candidate representatives include abstention and preserve bit sums" (∀ n : Nat, candidateCheck n = true) seed
  unless (List.range 256).all candidateCheck do
    throw (IO.userError "candidate-substitution backstop failed")
  IO.println "candidate-substitution backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.CandidateSubstitutionExperiments
