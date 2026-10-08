import ExplainableCrypto.Helios.Symbolic.GeneralCandidateProtection
import ExplainableCrypto.Helios.Symbolic.CandidateSubstitutionExperiments
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameExperiments

namespace ExplainableCrypto.Helios.Symbolic.GeneralCandidateExperiments
open ExplainableCrypto.Testing Historical HistoricalFrameExperiments

private def candidate (n : Nat) (abstain : Bool) (j : Fin (n + 1)) : BitCandidate n :=
  if abstain then .abstain n else .selected j

def frameCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let mode := seed / 5 % 4
  let swap := seed / 20 % 2 == 1
  let leftZero := mode % 2 == 0
  let rightZero := mode / 2 == 0
  let leftPos : Fin (n + 1) := ⟨seed / 40 % (n + 1), Nat.mod_lt _ (by omega)⟩
  let rightPos : Fin (n + 1) := ⟨seed / 80 % (n + 1), Nat.mod_lt _ (by omega)⟩
  let left := candidate n leftZero leftPos
  let right := candidate n rightZero rightPos
  let ns := generatedNames n
  let φ := General.frame ns swap left.substitution right.substitution
  (φ.value 0 == publicKey ns) && ((List.finRange 2).all fun voter =>
    let useRight := if voter.val = 0 then swap else !swap
    let abstain := if useRight then rightZero else leftZero
    let chosen := if useRight then rightPos else leftPos
    let ballot := φ.value voter.succ
    let fieldsOK := (List.finRange (n + 1)).all fun j =>
      let bit := if !abstain && j == chosen then Constant.one else .zero
      let c := Term.ternary .penc (publicKey ns) (.name (ns.nonce voter j)) (.const bit)
      let p := Term.spk (publicKey ns) (.name (ns.nonce voter j)) (.const bit) c
      (normalizeRaw (ballot.project j.val) == c) &&
        (normalizeRaw (ballot.project (n + 1 + j.val)) == p)
    let aggregateOK := match normalizeRaw (aggregateCiphertext n ballot) with
      | .ternary .penc k r m =>
        (k == publicKey ns) &&
          (r == foldCandidates .compose (fun j => .name (ns.nonce voter j))) &&
          (m.addSummary.atoms.card == 0) &&
          (m.addSummary.numeric == some (if abstain then 0 else 1))
      | _ => false
    fieldsOK && aggregateOK && (normalizeRaw (ballot.drop (fieldCount n)) == .const .bottom))

#eval do
  for seed in [1, 7, 42] do
    campaign "general honest frames include every abstention pair and swap" (∀ n : Nat, frameCheck n = true) seed
  unless (List.range 256).all frameCheck do
    throw (IO.userError "general-candidate-frame backstop failed")
  IO.println "general-candidate-frame backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.GeneralCandidateExperiments
