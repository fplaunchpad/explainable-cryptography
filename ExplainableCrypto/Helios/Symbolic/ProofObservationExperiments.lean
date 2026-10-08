import ExplainableCrypto.Helios.Symbolic.CiphertextObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.ProofObservationExperiments
open ExplainableCrypto.Testing Historical

private def candidate (n : Nat) (zero : Bool) (j : Fin (n + 1)) : BitCandidate n :=
  if zero then .abstain n else .selected j

/-- Compare actual normalized proof fields against an independent provenance
criterion, including the single-candidate component/aggregate coincidence. -/
def proofCheck (seed : Nat) (broken := false) : Bool :=
  let n := seed % 5
  let aggA := seed / 5 % 2 == 1
  let aggB := seed / 10 % 2 == 1
  let swap := seed / 20 % 2 == 1
  let i : Fin 2 := ⟨seed / 40 % 2, Nat.mod_lt _ (by decide)⟩
  let k : Fin 2 := ⟨seed / 80 % 2, Nat.mod_lt _ (by decide)⟩
  let j : Fin (n + 1) := ⟨seed / 160 % (n + 1), Nat.mod_lt _ (by omega)⟩
  let l : Fin (n + 1) := ⟨(seed / 160 + seed / 160 % 2) % (n + 1), Nat.mod_lt _ (by omega)⟩
  let ns := HistoricalFrameExperiments.generatedNames n
  let φ := General.frame ns swap (candidate n (seed % 2 == 0) j).substitution
    (candidate n (seed / 2 % 2 == 0) l).substitution
  let select := fun (v : Fin 2) (c : Fin (n + 1)) (agg : Bool) =>
    (Term.var v.succ : Recipe 3).project (if agg then 2 * (n + 1) else n + 1 + c.val)
  let actual := normalizeRaw (φ.eval (select i j aggA)) == normalizeRaw (φ.eval (select k l aggB))
  let expected := (i == k) && ((aggA && aggB) || (!aggA && !aggB && j == l) || (!broken && n == 0))
  actual == expected

#eval campaign "component and aggregate proof tags always differ (negative control)"
  (∀ n : Nat, proofCheck n true = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "actual honest proof equality follows nonce provenance and the one-candidate exception"
      (∀ n : Nat, proofCheck n = true) seed
  unless (List.range 256).all proofCheck do
    throw (IO.userError "proof-observation backstop failed")
  unless (List.range 640).all (fun n => proofCheck (160 + n)) do
    throw (IO.userError "proof-observation varied-position cases failed")
  IO.println "proof-observation backstop: 256 inputs and directed inputs 160 through 799 passed"

end ExplainableCrypto.Helios.Symbolic.ProofObservationExperiments
