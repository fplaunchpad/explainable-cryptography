import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.ComposeFactorExperiments
open ExplainableCrypto.Testing RewriteExperiments

def rawFactors : Term Nat → List (Term Nat)
  | .binary .compose a b => rawFactors a ++ rawFactors b
  | t => [t]

def rebuild : List (Term Nat) → Option (Term Nat)
  | [] => none
  | a :: rest => match rebuild rest with
    | none => some a
    | some b => some (.binary .compose a b)

#eval campaign "zero is a composition unit (negative control)"
  (∀ n : Nat, (rawFactors (.binary .compose (.name n) (.const .zero)) : Multiset (Term Nat)) =
    (rawFactors (.name n) : Multiset (Term Nat))) 1 true

def composeCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 11)
  let c := generatedTerm (n % 4) (n + 17)
  let source := Term.binary .compose a (.binary .compose b c)
  let rotated := Term.binary .compose c (.binary .compose b a)
  let expanded := Term.binary .compose (.name n) (.name (n + 1))
  let projected := Term.unary .fst (.binary .pair expanded (.const .bottom))
  ((rebuild (rawFactors source)).map rawFactors == some (rawFactors source)) &&
  decide ((rawFactors source : Multiset (Term Nat)) = rawFactors rotated) &&
  ((rawFactors (.binary .compose (.name n) (.name n))).length == 2) &&
  ((rootReduce projected).map Subtype.val == some expanded) &&
  ((rawFactors projected).length == 1) && ((rawFactors expanded).length == 2) &&
  ((rawFactors (.binary .mul a b)).length == 1) && (rebuild []).isNone

#eval do
  for seed in [1, 7, 42] do
    campaign "composition flattening preserves AC bags and expanding replacements"
      (∀ n : Nat, composeCheck n = true) seed
  unless (List.range 256).all composeCheck do
    throw (IO.userError "composition deterministic backstop failed")
  IO.println "composition deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ComposeFactorExperiments
