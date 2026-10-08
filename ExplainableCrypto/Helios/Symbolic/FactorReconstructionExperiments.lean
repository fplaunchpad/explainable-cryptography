import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.FactorReconstructionExperiments
open ExplainableCrypto.Testing RewriteExperiments

def rawFactors : Term Nat → List (Term Nat)
  | .binary .mul a b => rawFactors a ++ rawFactors b
  | t => [t]

/-- Empty products remain absent; no object-language sentinel is appended. -/
def rebuild : List (Term Nat) → Option (Term Nat)
  | [] => none
  | a :: rest => match rebuild rest with
    | none => some a
    | some b => some (.binary .mul a b)

#eval campaign "zero is a multiplication unit (negative control)"
  (∀ n : Nat, (rawFactors (.binary .mul (.name n) (.const .zero)) : Multiset (Term Nat)) =
    (rawFactors (.name n) : Multiset (Term Nat))) 1 true

def reconstructionCheck (n : Nat) : Bool :=
  let t := generatedTerm (n % 4) n
  let a : Term Nat := .ternary .penc (.name 0) (.name 1) (.const .zero)
  let b : Term Nat := .ternary .penc (.name 0) (.name 2) (.const .one)
  ((rebuild (rawFactors t)).map rawFactors == some (rawFactors t)) &&
  ((rawFactors (.binary .mul a (.binary .mul t b)) : Multiset (Term Nat)) ==
    (rawFactors (.binary .mul (.binary .mul a b) t) : Multiset (Term Nat))) &&
  (rawFactors (.binary .mul a a)).length == 2 &&
  (rebuild []).isNone && (rebuild [a] == some a)

#eval do
  for seed in [1, 7, 42] do
    campaign "factor reconstruction preserves nonempty syntax and pair selection"
      (∀ n : Nat, reconstructionCheck n = true) seed
  unless (List.range 256).all reconstructionCheck do
    throw (IO.userError "factor-reconstruction deterministic backstop failed")
  IO.println "factor-reconstruction deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.FactorReconstructionExperiments

namespace ExplainableCrypto.Helios.Symbolic.FactorReconstructionExperiments
open ExplainableCrypto.Testing RewriteExperiments

/-- Independent E7 outputs for two key groups; both reductions must succeed. -/
def disjointCheck (n : Nat) : Bool :=
  let r := generatedTerm (n % 4) n
  let s := generatedTerm (n % 4) (n + 13)
  let a : Term Nat := .ternary .penc (.name 0) r (.const .zero)
  let b : Term Nat := .ternary .penc (.name 0) s (.const .one)
  let c : Term Nat := .ternary .penc (.name 1) r (.const .one)
  let d : Term Nat := .ternary .penc (.name 1) s (.const .zero)
  let ab : Term Nat := .ternary .penc (.name 0) (.binary .compose r s) (.binary .add (.const .zero) (.const .one))
  let cd : Term Nat := .ternary .penc (.name 1) (.binary .compose r s) (.binary .add (.const .one) (.const .zero))
  ((rootReduce (.binary .mul a b)).map Subtype.val == some ab) &&
  ((rootReduce (.binary .mul c d)).map Subtype.val == some cd) &&
  ((rawFactors (.binary .mul ab cd) : Multiset (Term Nat)) ==
    (rawFactors (.binary .mul cd ab) : Multiset (Term Nat))) &&
  (rootReduce (.binary .mul a c)).isNone

#eval do
  for seed in [1, 7, 42] do
    campaign "two key groups combine independently and retain both outputs"
      (∀ n : Nat, disjointCheck n = true) seed
  unless (List.range 256).all disjointCheck do
    throw (IO.userError "disjoint-selection deterministic backstop failed")
  IO.println "disjoint-selection deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.FactorReconstructionExperiments
