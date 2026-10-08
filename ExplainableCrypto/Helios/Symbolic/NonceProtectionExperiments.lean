import ExplainableCrypto.Helios.Symbolic.NonceProtection
import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.NonceProtectionExperiments
open ExplainableCrypto.Testing RewriteExperiments

def protectedCipher (n : Nat) : Term Nat :=
  .ternary .penc (.unary .pk (.name (n + 1))) (.name n) (.const .one)

def leakage (n : Nat) : Term Nat := .binary .dec (.name (n + 1))
  (.ternary .penc (.unary .pk (.name (n + 1))) (.name (n + 2)) (.name n))

def protectionCheck (n : Nat) : Bool :=
  let c := protectedCipher n
  let proof := Term.spk (.name n) (.name n) (.name n) c
  let publicTerm := generatedTerm (n % 4) (n + 7)
  let safePublic := Term.unary .pk publicTerm
  let terms := [c, proof, safePublic, .unary .fst (.binary .pair c proof),
    .binary .dec (.name (n + 1)) c, .binary .mul c c,
    .binary .dec (.binary .partialDecrypt (.name (n + 1)) c) c]
  terms.all (fun t => t.nonceSafe {n} && (normalizeRaw t).nonceSafe {n}) &&
  (!(leakage n).nonceSafe {n}) && (normalizeRaw (leakage n) == .name n)

#eval campaign "ciphertext plaintext can be ignored (negative control)"
  (∀ n : Nat, (normalizeRaw (leakage n)).nonceSafe {n} = true) 1 true

#eval campaign "full-E expansion preserves protection (negative control)"
  (∀ n : Nat, (Term.unary .fst (.binary .pair (.const .one) (.name n)) : Term Nat).nonceSafe {n} = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "protected nonce positions survive public reductions"
      (∀ n : Nat, protectionCheck n = true) seed
  unless (List.range 256).all protectionCheck do
    throw (IO.userError "nonce protection backstop failed")
  IO.println "nonce protection backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.NonceProtectionExperiments
