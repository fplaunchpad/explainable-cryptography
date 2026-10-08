import ExplainableCrypto.Testing.Plausible
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Multiset.Dedup

namespace ExplainableCrypto.Helios.Symbolic.PairSelectionExperiments
open ExplainableCrypto.Testing

#eval campaign "deduplication preserves a two-occurrence selection (negative control)"
  (∀ n : Nat, (Multiset.dedup ({n, n} : Multiset Nat)).card = 2) 1 true

/-- Selections come from two distinct positions each. Repeated values are allowed. -/
def classificationCheck (n : Nat) : Bool :=
  let len := 4 + n % 5
  let xs := (List.range len).map (fun i => (n / (i + 1) + i) % 4)
  let i := n % len
  let j := (i + 1 + (n / 7) % (len - 1)) % len
  let k := (n / 11) % len
  let l := (k + 1 + (n / 13) % (len - 1)) % len
  let source : Multiset Nat := xs
  let p : Multiset Nat := {xs[i]!, xs[j]!}
  let q : Multiset Nat := {xs[k]!, xs[l]!}
  let shared := p ∩ q
  let rest := source - (p ∪ q)
  decide (i ≠ j ∧ k ≠ l ∧ p ≤ source ∧ q ≤ source ∧ p.card = 2 ∧ q.card = 2 ∧
    ((shared.card = 2 ∧ p = q) ∨
     (shared.card = 1 ∧ (p - shared).card = 1 ∧ (q - shared).card = 1 ∧
       source = shared + (p - shared) + (q - shared) + rest) ∨
     (shared.card = 0 ∧ source = p + q + rest)))

#eval do
  for seed in [1, 7, 42] do
    campaign "two-occurrence selections admit identical/shared/disjoint decompositions"
      (∀ n : Nat, classificationCheck n = true) seed
  unless (List.range 256).all classificationCheck do
    throw (IO.userError "pair-selection deterministic backstop failed")
  IO.println "pair-selection deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.PairSelectionExperiments
