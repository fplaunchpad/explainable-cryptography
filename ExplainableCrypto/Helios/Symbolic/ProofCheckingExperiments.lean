import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.ProofCheckingExperiments
open ExplainableCrypto.Testing RewriteExperiments

def ballot (k r : Term Nat) (bit : Constant) : Term Nat := .ternary .penc k r (.const bit)
def proofTerm (k r : Term Nat) (bit : Constant) : Term Nat := .spk k r (.const bit) (ballot k r bit)
def checkTerm (k r : Term Nat) (bit : Constant) : Term Nat := .ternary .checkspk k (ballot k r bit) (proofTerm k r bit)

#eval campaign "proof checking ignores the bound ciphertext (negative control)"
  (∀ n : Nat, (rootReduce (Term.ternary .checkspk (.name 0) (ballot (.name 0) (.name n) .zero)
    (.spk (.name 0) (.name n) (.const .zero) (ballot (.name 0) (.name (n + 1)) .zero)))).isSome = true) 1 true

def expectedBits (k r : Term Nat) : Bool :=
  ((rootReduce (checkTerm k r .zero)).map Subtype.val == some (.const .ok)) &&
  ((rootReduce (checkTerm k r .one)).map Subtype.val == some (.const .ok)) &&
  (rootReduce (checkTerm k r .ok)).isNone && (rootReduce (checkTerm k r .bottom)).isNone &&
  (rootReduce (.ternary .checkspk k (ballot k r .zero) (proofTerm k r .one))).isNone

def checkingCheck (n : Nat) : Bool :=
  let k := generatedTerm (n % 4) n
  let r := generatedTerm (n % 4) (n + 13)
  let s := generatedTerm (n % 4) (n + 19)
  let m := generatedTerm (n % 4) (n + 23)
  (reductionPairs k r s m (.const .one)).all (fun (a, b) =>
    ((rootReduce a).map Subtype.val == some b) &&
    expectedBits a r && expectedBits b r && expectedBits k a && expectedBits k b &&
    (rootReduce (.ternary .checkspk k (ballot k a .zero)
      (.spk k a (.const .zero) (ballot k b .zero)))).isNone)

#eval do
  for seed in [1, 7, 42] do
    campaign "E8/E9 synchronization preserves bits and bound-ciphertext checks"
      (∀ n : Nat, checkingCheck n = true) seed
  unless (List.range 256).all checkingCheck do
    throw (IO.userError "proof-checking deterministic backstop failed")
  IO.println "proof-checking deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ProofCheckingExperiments
