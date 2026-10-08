import ExplainableCrypto.Helios.Symbolic.SuccessfulCheckSPOT
import ExplainableCrypto.Helios.Symbolic.DecryptionProbeExperiments

namespace ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionExperiments
open ExplainableCrypto.Testing
private def wrap (t : Recipe 3) := Term.unary .fst (.binary .pair t (.const .bottom))

def check (seed : Nat) : Bool :=
  let secret : Recipe 3 := if seed%2=0 then .name 40
    else .binary .partialDecrypt (.name 40) (.var 0)
  let payload : Recipe 3 := if seed%3=0 then .var 1 else if seed%3=1 then
    .binary .pair (.name 90) (.var 2) else .binary .add (.const .one) (.const .one)
  let key := Term.unary .pk (wrap secret)
  let c := Term.ternary .penc key (.name (50+seed%4)) payload
  let a := if seed%2=0 then wrap secret else .binary .partialDecrypt (wrap secret) (wrap c)
  let whole := Term.binary .dec a c
  decide (payload.nodeCount<whole.nodeCount) &&
    DecryptionProbeExperiments.sizeCheck seed &&
    DecryptionProbeExperiments.probeCheck seed &&
    [false,true].all (fun swap =>
      let φ := LocalRootSPOT.world swap
      normalizeRaw (φ.eval whole) == normalizeRaw (φ.eval payload))

#eval campaign "successful decryption omitting E5 (negative control)"
  (∀ n : Nat, DecryptionProbeExperiments.omitDirect n = true) 1 true
#eval campaign "successful decryption omitting ciphertext binding (negative control)"
  (∀ n : Nat, DecryptionProbeExperiments.omitBinding n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "successful decryption returns explicit payload with smaller probes"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "successful decryption backstop failed")
  IO.println "successful decryption backstop: 2048 inputs, both rules, nested keys, nonconstant payloads and both swaps"

end ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionExperiments
