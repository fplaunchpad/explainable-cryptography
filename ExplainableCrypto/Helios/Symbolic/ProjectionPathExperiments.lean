import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.ProjectionPathExperiments
open ExplainableCrypto.Testing RewriteExperiments

def reveal (a b : Term Nat) : Term Nat := .unary .fst
  (.binary .pair (.binary .pair a b) (.const .bottom))

def pathCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 11)
  (normalizeRaw (.unary .pk a) == .unary .pk (normalizeRaw a)) &&
  (normalizeRaw (.unary .fst (reveal a b)) == normalizeRaw a) &&
  (normalizeRaw (.unary .snd (reveal a b)) == normalizeRaw b) &&
  (normalizeRaw (.unary .fst (.name n)) == (.unary .fst (.name n) : Term Nat))

def isPair : Term Nat → Bool
  | .binary .pair _ _ => true
  | _ => false

#eval campaign "successful projection requires an initial literal pair (negative control)"
  (∀ n : Nat, isPair (reveal (.name n) (.name (n + 1))) = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "public-key and revealed-pair projection paths"
      (∀ n : Nat, pathCheck n = true) seed
  unless (List.range 256).all pathCheck do
    throw (IO.userError "projection path backstop failed")
  IO.println "projection path backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ProjectionPathExperiments
