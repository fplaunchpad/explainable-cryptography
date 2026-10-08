import ExplainableCrypto.Helios.Symbolic.BaseStructure
import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.HomomorphicRootExperiments
open ExplainableCrypto.Testing RewriteExperiments

/-- Decidable approximation of quotient factors, retaining only their head tags. -/
def factorTags : Term Nat → List (HeadTag Nat)
  | .binary .mul a b => factorTags a ++ factorTags b
  | t => [t.headTag]

#eval campaign "ordered multiplication factors are E0-invariant (negative control)"
  (∀ n : Nat, factorTags (.binary .mul (.name n) (.name (n + 1))) =
    factorTags (.binary .mul (.name (n + 1)) (.name n))) 1 true

def factorsCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 13)
  let c := generatedTerm (n % 4) (n + 29)
  (backgroundPairs a b c).all (fun (l, r) =>
    (factorTags l : Multiset (HeadTag Nat)) == (factorTags r : Multiset (HeadTag Nat))) &&
  (factorTags (.name n) != factorTags (.name (n + 1)))

#eval do
  for seed in [1, 7, 42] do
    campaign "unordered multiplication factor tags respect E0 fixtures"
      (∀ n : Nat, factorsCheck n = true) seed
  unless (List.range 256).all factorsCheck do
    throw (IO.userError "homomorphic-root deterministic backstop failed")
  IO.println "homomorphic-root deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.HomomorphicRootExperiments
