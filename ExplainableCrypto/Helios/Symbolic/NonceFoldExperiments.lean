import ExplainableCrypto.Helios.Symbolic.BallotValueExperiments
import ExplainableCrypto.Helios.Symbolic.ComposeFactorExperiments

namespace ExplainableCrypto.Helios.Symbolic.NonceFoldExperiments
open ExplainableCrypto.Testing Historical

private def other (seed k : Nat) : Ground :=
  let a := Term.name (60 + k)
  let b := Term.name (61 + k)
  match (seed + k) % 3 with
  | 0 => a
  | 1 => .binary .compose a b
  | _ => .unary .fst (.binary .pair (.binary .compose a b) (.const .bottom))

def foldCheck (seed : Nat) : Bool :=
  let n := 1 + seed % 4
  let honest := foldCandidates (n := n) .compose (fun j => (Term.name (20 + j.val % 2) : Ground))
  (List.finRange (n + 1)).all fun selected =>
    let xs := fun j => if j = selected then honest else other seed j.val
    let total := foldCandidates .compose xs
    let numeric := ((List.finRange (n + 1)).map (fun j => (xs j).composeFactors.card)).sum
    let reduced := normalizeRaw total
    (honest.composeFactors.card == n + 1) &&
      (total.composeFactors.card == numeric) &&
      (n + honest.composeFactors.card ≤ total.composeFactors.card) &&
      (n + 1 < total.composeFactors.card) &&
      (total.composeFactors.card ≤ reduced.composeFactors.card) &&
      (total.nonceSafe {20, 21} == false) && (reduced.nonceSafe {20, 21} == false)

#eval campaign "full-E raw composition-card upper bound without normal target (negative control)"
  (∀ n : Nat,
    (Term.binary .compose (.name n) (.name n) : Ground).composeFactors.card ≤
      (Term.unary .fst (.binary .pair (.binary .compose (.name n) (.name n)) (.const .bottom)) : Ground).composeFactors.card)
  1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "nonce fold counts, multiplicity and expanding components" (∀ n : Nat, foldCheck n = true) seed
  unless (List.range 256).all foldCheck do
    throw (IO.userError "nonce-fold backstop failed")
  IO.println "nonce-fold backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.NonceFoldExperiments
