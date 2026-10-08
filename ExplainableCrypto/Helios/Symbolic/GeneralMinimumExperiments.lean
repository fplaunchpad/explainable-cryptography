import ExplainableCrypto.Helios.Symbolic.GeneralCandidateSPOT
import ExplainableCrypto.Helios.Symbolic.MinimumOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.GeneralMinimumExperiments
open ExplainableCrypto.Testing Historical MinimumOriginExperiments GeneralCandidateSPOT

private def candidate (mode : Nat) (isLeft : Bool) : CandidateSubstitution 1 Empty :=
  if isLeft then (if mode < 2 then abstain else represented)
  else (if mode % 2 = 0 then abstain else (BitCandidate.selected (0 : Fin 2)).substitution)

private def generalCertificate (σ : Fin 3 → Ground) (key : Ground) (r : Recipe 3) : Bool :=
  match r with
  | .ternary .penc k _ _ => normalizeRaw (k.subst σ) == key
  | .binary .mul a b => generalCertificate σ key a && generalCertificate σ key b
  | _ => match normalizeRaw (r.subst σ) with
    | .ternary .penc k _ m => chain r && k == key && 1 < r.nodeCount &&
        m.addSummary.atoms.card == 0 && (m.addSummary.numeric == some 0 || m.addSummary.numeric == some 1)
    | _ => false

def generalOriginCheck (seed : Nat) : Bool :=
  let mode := seed / 8 % 4
  let σ := (General.frame names (seed / 4 % 2 == 1) (candidate mode true) (candidate mode false)).value
  let entries := (catalogue seed).map (fun r => (r, normalizeRaw (r.subst σ)))
  entries.all (fun (r, value) =>
    entries.any (fun (s, other) => s.nodeCount < r.nodeCount && other == value) ||
    (match value with
      | .binary .pair _ _ => pairOrigin r
      | .ternary .penc key _ _ => generalCertificate σ key r
      | .spk _ _ _ _ => proofOrigin r
      | _ => true))

#eval do
  for seed in [1, 7, 42] do
    campaign "general candidate finite-catalogue minimum origins" (∀ n : Nat, generalOriginCheck n = true) seed
  unless (List.range 256).all generalOriginCheck do
    throw (IO.userError "general minimum-origin backstop failed")
  IO.println "general minimum-origin backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.GeneralMinimumExperiments
