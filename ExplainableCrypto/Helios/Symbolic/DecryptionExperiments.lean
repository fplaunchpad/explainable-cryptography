import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.DecryptionExperiments
open ExplainableCrypto.Testing RewriteExperiments

def cipher (k r m : Term Nat) : Term Nat := .ternary .penc (.unary .pk k) r m
def direct (k r m : Term Nat) : Term Nat := .binary .dec k (cipher k r m)
def partialSource (k r m : Term Nat) : Term Nat :=
  .binary .dec (.binary .partialDecrypt k (cipher k r m)) (cipher k r m)

#eval campaign "one changed E6 ciphertext still root-matches (negative control)"
  (∀ n : Nat, (rootReduce (.binary .dec
    (.binary .partialDecrypt (.name 0) (cipher (.name 0) (.name 1) (.name n)))
    (cipher (.name 0) (.name 1) (.name (n + 1))))).isSome = true) 1 true

def outputsMatch (k r m : Term Nat) : Bool :=
  ((rootReduce (direct k r m)).map Subtype.val == some m) &&
  ((rootReduce (partialSource k r m)).map Subtype.val == some m)

def decryptionCheck (n : Nat) : Bool :=
  let k := generatedTerm (n % 4) n
  let r := generatedTerm (n % 4) (n + 13)
  let s := generatedTerm (n % 4) (n + 19)
  let m := generatedTerm (n % 4) (n + 23)
  (reductionPairs k r s m (.const .one)).all (fun (a, b) =>
    ((rootReduce a).map Subtype.val == some b) &&
    outputsMatch a r m && outputsMatch b r m &&
    outputsMatch k a m && outputsMatch k b m &&
    outputsMatch k r a && outputsMatch k r b &&
    (rootReduce (.binary .dec (.binary .partialDecrypt k (cipher k r a)) (cipher k r b))).isNone)

#eval do
  for seed in [1, 7, 42] do
    campaign "E5/E6 synchronized parameter changes return the expected plaintext"
      (∀ n : Nat, decryptionCheck n = true) seed
  unless (List.range 256).all decryptionCheck do
    throw (IO.userError "decryption deterministic backstop failed")
  IO.println "decryption deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.DecryptionExperiments
