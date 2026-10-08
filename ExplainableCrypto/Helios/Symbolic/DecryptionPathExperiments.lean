import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.RawNormalization

namespace ExplainableCrypto.Helios.Symbolic.DecryptionPathExperiments
open ExplainableCrypto.Testing RewriteExperiments

def reveal (a : Term Nat) : Term Nat := .unary .fst (.binary .pair a (.const .bottom))
def enc (k r m : Term Nat) : Term Nat := .ternary .penc (.unary .pk k) r m

def pathCheck (seed : Nat) : Bool :=
  let k := generatedTerm (seed % 4) seed
  let r := generatedTerm (seed % 4) (seed + 13)
  let m := generatedTerm (seed % 4) (seed + 23)
  let c := enc k r (reveal m)
  let direct := Term.binary .dec (reveal k) (reveal c)
  let viaPartial := Term.binary .dec
    (reveal (.binary .partialDecrypt (reveal k) (reveal c))) (reveal (reveal c))
  (normalizeRaw direct == normalizeRaw m) &&
    (normalizeRaw viaPartial == normalizeRaw m)

#eval campaign "revealed ciphertext already has initial penc syntax (negative control)"
  (∀ n : Nat,
    let c := enc (.name 0) (.name 1) (enc (.name 2) (.name 3) (.name n))
    (match reveal c with | .ternary .penc _ _ _ => true | _ => false) = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "delayed E5/E6 matches select the expected plaintext"
      (∀ n : Nat, pathCheck n = true) seed
  unless (List.range 256).all pathCheck do
    throw (IO.userError "decryption path backstop failed")
  IO.println "decryption path backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.DecryptionPathExperiments
