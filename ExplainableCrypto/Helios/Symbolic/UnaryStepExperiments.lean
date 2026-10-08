import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.UnaryStepExperiments
open ExplainableCrypto.Testing RewriteExperiments

#eval campaign "fst and snd return the same pair member (negative control)"
  (∀ n : Nat, (rootReduce (Term.unary .fst (.binary .pair (.name n) (.name (n + 1))) : Term Nat)).map Subtype.val =
    (rootReduce (.unary .snd (.binary .pair (.name n) (.name (n + 1))) : Term Nat)).map Subtype.val) 1 true

def projectionCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 11)
  let c := generatedTerm (n % 4) (n + 17)
  let q := generatedTerm (n % 4) (n + 23)
  (reductionPairs a b c q (.const .one)).all (fun (l, r) =>
    ((rootReduce l).map Subtype.val == some r) &&
    ((rootReduce (.unary .fst (.binary .pair l b))).map Subtype.val == some l) &&
    ((rootReduce (.unary .fst (.binary .pair r b))).map Subtype.val == some r) &&
    ((rootReduce (.unary .snd (.binary .pair l b))).map Subtype.val == some b) &&
    ((rootReduce (.unary .snd (.binary .pair r b))).map Subtype.val == some b) &&
    ((rootReduce (.unary .fst (.binary .pair b l))).map Subtype.val == some b) &&
    ((rootReduce (.unary .fst (.binary .pair b r))).map Subtype.val == some b) &&
    ((rootReduce (.unary .snd (.binary .pair b l))).map Subtype.val == some l) &&
    ((rootReduce (.unary .snd (.binary .pair b r))).map Subtype.val == some r))

#eval do
  for seed in [1, 7, 42] do
    campaign "ordered projections preserve selected and discarded member behavior"
      (∀ n : Nat, projectionCheck n = true) seed
  unless (List.range 256).all projectionCheck do
    throw (IO.userError "projection deterministic backstop failed")
  IO.println "projection deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.UnaryStepExperiments
