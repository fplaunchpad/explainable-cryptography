import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.VariableOverlapExperiments
open ExplainableCrypto.Testing RewriteExperiments

def projected (x : Term Nat) : Term Nat := .unary .fst (.binary .pair x (.const .bottom))

def mismatchedDecrypt (k r m : Term Nat) : Term Nat :=
  .binary .dec k (.ternary .penc (.unary .pk (projected k)) r m)

#eval campaign "one changed key copy still root-matches (negative control)"
  (∀ n : Nat, (rootReduce (mismatchedDecrypt (.name n) (.name 1) (.const .one))).isSome = true)
  1 true

/-- Both root routes are matched independently; expected outputs are the seven
source-rule right sides. Projection supplies a reachable parameter reduction. -/
def synchronisationCheck (n : Nat) : Bool :=
  let k := generatedTerm (n % 4) n
  let r := generatedTerm (n % 4) (n + 13)
  let s := generatedTerm (n % 4) (n + 19)
  let m := generatedTerm (n % 4) (n + 23)
  let q := generatedTerm (n % 4) (n + 31)
  ((rootReduce (projected k)).map Subtype.val == some k) &&
  (reductionPairs (projected k) r s m q).all
    (fun (l, rhs) => (rootReduce l).map Subtype.val == some rhs) &&
  (reductionPairs k r s m q).all
    (fun (l, rhs) => (rootReduce l).map Subtype.val == some rhs) &&
  ((rootReduce (mismatchedDecrypt (.name n) r m)).isNone)

#eval do
  for seed in [1, 7, 42] do
    campaign "synchronised variable instances match all seven root rules"
      (∀ n : Nat, synchronisationCheck n = true) seed
  unless (List.range 256).all synchronisationCheck do
    throw (IO.userError "variable-overlap deterministic backstop failed")
  IO.println "variable-overlap deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.VariableOverlapExperiments
