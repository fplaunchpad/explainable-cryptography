import ExplainableCrypto.Helios.Symbolic.CiphertextCombinationExperiments

namespace ExplainableCrypto.Helios.Symbolic.SeparatedNonceExperiments
open ExplainableCrypto.Testing

def separatedCheck (seed : Nat) : Bool :=
  let r := [40 + seed % 3, 44 + seed / 3 % 3]
  let s := if seed % 3 = 0 then r.reverse else [40 + seed % 3]
  let a := [20 + seed / 5 % 5, 20 + seed / 7 % 5, 20 + seed / 5 % 5]
  let b := if seed / 3 % 2 = 0 then a.reverse else a.take 2
  decide ((r ++ a).Perm (s ++ b) ↔ r.Perm s ∧ a.Perm b)

def unprotectedCheck (seed : Nat) : Bool :=
  let a := 20 + seed % 5
  let b := a + 1
  decide (([b] ++ [a]).Perm ([a] ++ [b]) ↔ ([a] : List Nat).Perm [b])

#eval campaign "mixed nonce cancellation without protection (negative control)"
  (∀ n : Nat, unprotectedCheck n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "separated nonce bags retain remainders and multiplicity"
      (∀ n : Nat, separatedCheck n = true) seed
  unless (List.range 256).all separatedCheck do
    throw (IO.userError "separated-nonce backstop failed")
  IO.println "separated-nonce backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.SeparatedNonceExperiments
