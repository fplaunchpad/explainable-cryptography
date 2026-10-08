import ExplainableCrypto.Helios.Symbolic.VariableOverlapExperiments

namespace ExplainableCrypto.Helios.Symbolic.CiphertextStepExperiments
open ExplainableCrypto.Testing RewriteExperiments VariableOverlapExperiments

def cipher (k r m : Term Nat) : Term Nat := .ternary .penc k r m
def fusion (k r s m n : Term Nat) : Term Nat :=
  .binary .mul (cipher k r m) (cipher k s n)
def expected (k r s m n : Term Nat) : Term Nat :=
  cipher k (.binary .compose r s) (.binary .add m n)

#eval campaign "one changed fusion key still matches (negative control)"
  (∀ n : Nat, (rootReduce (.binary .mul
    (cipher (.name n) (.name 1) (.const .zero))
    (cipher (projected (.name n)) (.name 2) (.const .one)))).isSome = true) 1 true

/-- Independent expected E7 outputs before/after reachable component changes.
The seven root-rule families provide changes rather than arbitrary term pairs. -/
def mixedCheck (n : Nat) : Bool :=
  let k := generatedTerm (n % 4) n
  let r := generatedTerm (n % 4) (n + 13)
  let s := generatedTerm (n % 4) (n + 19)
  let m := generatedTerm (n % 4) (n + 23)
  let q := generatedTerm (n % 4) (n + 31)
  (reductionPairs k r s m q).all (fun (a, b) =>
    ((rootReduce a).map Subtype.val == some b) &&
    ((rootReduce (fusion a r s m q)).map Subtype.val == some (expected a r s m q)) &&
    ((rootReduce (fusion b r s m q)).map Subtype.val == some (expected b r s m q)) &&
    ((rootReduce (fusion k a s m q)).map Subtype.val == some (expected k a s m q)) &&
    ((rootReduce (fusion k b s m q)).map Subtype.val == some (expected k b s m q)) &&
    ((rootReduce (fusion k r s a q)).map Subtype.val == some (expected k r s a q)) &&
    ((rootReduce (fusion k r s b q)).map Subtype.val == some (expected k r s b q))) &&
  (rootReduce (.binary .mul (cipher k r m) (cipher (projected k) s q))).isNone

#eval do
  for seed in [1, 7, 42] do
    campaign "fusion component changes have the expected synchronized root outputs"
      (∀ n : Nat, mixedCheck n = true) seed
  unless (List.range 256).all mixedCheck do
    throw (IO.userError "ciphertext component deterministic backstop failed")
  IO.println "ciphertext component deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.CiphertextStepExperiments
