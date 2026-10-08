import ExplainableCrypto.Helios.Symbolic.HistoricalFrameExperiments
import ExplainableCrypto.Helios.Symbolic.AddSummary

namespace ExplainableCrypto.Helios.Symbolic.HistoricalValidityExperiments
open ExplainableCrypto.Testing Historical HistoricalFrameExperiments

def validityCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let ns := generatedNames n
  (List.finRange (n + 1)).all fun chosen =>
    let cs := foldCandidates .mul (ciphertext ns 0 chosen)
    let rs := foldCandidates .compose (fun j => Term.name (ns.nonce 0 j))
    let ms := foldCandidates .add (vote chosen)
    (normalizeRaw cs == .ternary .penc (publicKey ns) rs ms) &&
    (normalizeRaw ((ballot ns 0 chosen).project (2 * (n + 1))) == normalizeRaw (aggregateProof ns 0 chosen)) &&
    ((List.finRange (n + 1)).all fun j =>
      normalizeRaw ((ballot ns 0 chosen).project (n + 1 + j.val)) == normalizeRaw (componentProof ns 0 chosen j))

#eval campaign "two selected votes collapse to one (negative control)"
  (∀ n : Nat, (AddSummary.number 1 : AddSummary Nat).combine (AddSummary.number (n + 1)) = AddSummary.number 1) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "honest aggregate folding and proof-field offsets"
      (∀ n : Nat, validityCheck n = true) seed
  unless (List.range 256).all validityCheck do
    throw (IO.userError "honest validity backstop failed")
  IO.println "honest validity backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.HistoricalValidityExperiments
