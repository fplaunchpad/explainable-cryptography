import ExplainableCrypto.Helios.Symbolic.ValueShapeExperiments

namespace ExplainableCrypto.Helios.Symbolic.CompositionObservationExperiments
open ExplainableCrypto.Testing
private def leaves : Ground → List Ground
  | .binary .compose a b => leaves a ++ leaves b
  | t => [t]
private def reveal (t : Ground) := Term.unary .fst (.binary .pair t (.const .bottom))
private def atom (seed : Nat) : Ground :=
  let x := Term.name (40 + seed / 4 % 4)
  match seed % 4 with
  | 0 => x | 1 => .unary .pk x | 2 => .binary .pair x (.name 50) | _ => .unary .fst x

def factorCheck (seed : Nat) : Bool :=
  let a := atom seed
  let b := atom (seed / 16)
  let x := Term.binary .compose (reveal a) (.binary .compose (reveal b) (reveal a))
  let y := Term.binary .compose (.binary .compose a a) b
  decide ((leaves (normalizeRaw x)).Perm [a,b,a]) &&
    decide ((leaves (normalizeRaw x)).Perm (leaves (normalizeRaw y))) &&
    decide (¬ (leaves (normalizeRaw x)).Perm [a,b]) &&
    decide ((leaves x).map normalizeRaw = leaves (normalizeRaw x))

def hiddenComposition (_seed : Nat) : Bool :=
  let b : Ground := .binary .compose (.name 40) (.name 41)
  let a := reveal b
  (normalizeRaw a == normalizeRaw b) == decide (((leaves a).map normalizeRaw).Perm ((leaves b).map normalizeRaw))

def eraseDuplicates (_seed : Nat) : Bool :=
  let a : Ground := .binary .compose (.name 40) (.name 40)
  decide ((leaves a).Perm ((leaves a).eraseDups))

#eval campaign "composition factors without non-composition premise (negative control)" (∀ n : Nat, hiddenComposition n = true) 1 true
#eval campaign "composition duplicate deletion (negative control)" (∀ n : Nat, eraseDuplicates n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "reducible composition factors retain permutation and multiplicity" (∀ n : Nat, factorCheck n = true) seed
  unless (List.range 1024).all factorCheck do
    throw (IO.userError "composition observation backstop failed")
  IO.println "composition observation backstop: 1024 inputs passed"

end ExplainableCrypto.Helios.Symbolic.CompositionObservationExperiments
