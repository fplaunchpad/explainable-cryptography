import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.OpaqueProtection
import ExplainableCrypto.Helios.Symbolic.TrusteePartialExperiments

namespace ExplainableCrypto.Helios.Symbolic.OpaqueProtectionExperiments
open ExplainableCrypto.Testing Historical General RewriteExperiments

def pairLeak (n : Nat) : Term Nat := .unary .fst (.binary .pair (.name n) (.const .one))
def plaintextLeak (n : Nat) : Term Nat :=
  let c := keyCiphertext (.name (n+1)) (.name (n+2)) (.name n)
  .binary .dec (.binary .partialDecrypt (.name (n+1)) c) c

def check (seed : Nat) : Bool :=
  let hidden := generatedTerm (seed%4) (seed+7)
  let part : Term Nat := .binary .partialDecrypt (.name seed) hidden
  let payload : Term Nat := .binary .pair (.const (if seed%2=0 then .zero else .one)) (.name (seed+1))
  let cipher := keyCiphertext part (.name seed) payload
  let bound := Term.binary .partialDecrypt part cipher
  let terms := [part, .unary .pk hidden, .spk hidden hidden hidden hidden,
    cipher, bound, .binary .dec part cipher, .binary .dec bound cipher,
    .binary .mul cipher cipher, .unary .fst (.binary .pair part payload),
    .unary .snd (.binary .pair part payload), .binary .compose part payload,
    .binary .add part payload, .ternary .checkspk part cipher bound]
  terms.all (fun t => t.opaqueSafe {seed} && (normalizeRaw t).opaqueSafe {seed}) &&
  (!(pairLeak seed).opaqueSafe {seed}) && (normalizeRaw (pairLeak seed) == .name seed) &&
  (!(plaintextLeak seed).opaqueSafe {seed}) && (normalizeRaw (plaintextLeak seed) == .name seed) &&
  [false,true].all (fun swap =>
    let rs := (List.range (seed%6)).map (fun i => ElectionTallyExperiments.publicBallot (40+i)
      (if (seed+i)%2=0 then .zero else .one))
    let f := finalFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight rs
    (List.finRange 5).all (fun i => (normalizeRaw (f.value i)).opaqueSafe ProofObservationSPOT.oneNames.restricted) &&
    let g := finalFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
    (List.finRange 5).all (fun i => (normalizeRaw (g.value i)).opaqueSafe LocalRootSPOT.names.restricted))

#eval campaign "pair fields may be treated as opaque (negative control)"
  (∀ n : Nat, (normalizeRaw (pairLeak n)).opaqueSafe {n} = true) 1 true
#eval campaign "E6 ciphertext plaintext may be treated as opaque (negative control)"
  (∀ n : Nat, (normalizeRaw (plaintextLeak n)).opaqueSafe {n} = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "opaque partials preserve names through nested reductions and publication"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "opaque protection backstop failed")
  IO.println "opaque protection backstop: 2048 inputs, nested constructors, E5/E6, one/two candidates, both swaps"

end ExplainableCrypto.Helios.Symbolic.OpaqueProtectionExperiments
