import ExplainableCrypto.Helios.Symbolic.ProofObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.PublicKeyObservationExperiments
open ExplainableCrypto.Testing Historical

private def chain : Nat → Nat → Recipe 3
  | 0, seed => .var ⟨seed % 3, Nat.mod_lt _ (by decide)⟩
  | d + 1, seed => .unary (if seed % 2 = 0 then .fst else .snd) (chain d (seed / 2))
private def isPk : Ground → Bool
  | .unary .pk _ => true
  | _ => false
private def keyForm : Recipe 3 → Bool
  | .unary .pk _ => true
  | .var i => i == 0
  | _ => false

def chainCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let ns := HistoricalFrameExperiments.generatedNames n
  let left := (BitCandidate.abstain n).substitution
  let right := (BitCandidate.selected (0 : Fin (n + 1))).substitution
  let φ := General.frame ns (seed / 5 % 2 == 1) left right
  let r := chain (seed / 10 % 5) (seed / 50)
  isPk (normalizeRaw (φ.eval r)) == (r == .var 0)

def constructorCheck (seed : Nat) : Bool :=
  let ns := HistoricalFrameExperiments.generatedNames 0
  let abstain := (BitCandidate.abstain 0).substitution
  let φ := General.frame ns (seed % 2 == 0) abstain abstain
  let freshName := Term.name (V := Fin 3) (40 + seed % 5)
  let wrapper := Term.unary .fst (.binary .pair freshName (.const .bottom))
  let a := normalizeRaw (φ.eval (.unary .pk freshName))
  let b := normalizeRaw (φ.eval (.unary .pk wrapper))
  (a == b) && (a != φ.eval (.var 0))

def nonminimumOriginCheck (seed : Nat) : Bool :=
  let φ := General.frame (HistoricalFrameExperiments.generatedNames 0) false
    (BitCandidate.abstain 0).substitution (BitCandidate.abstain 0).substitution
  let r : Recipe 3 := .unary .fst (.binary .pair (.unary .pk (.name (40 + seed % 5))) (.const .bottom))
  !(isPk (normalizeRaw (φ.eval r))) || keyForm r

#eval campaign "key-valued origins without minimum size (negative control)"
  (∀ n : Nat, nonminimumOriginCheck n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "actual frame projection chains expose only the published key handle"
      (∀ n : Nat, chainCheck n = true) seed
    campaign "public key construction respects reducible arguments and separates the election key"
      (∀ n : Nat, constructorCheck n = true) seed
  unless (List.range 256).all (fun n => chainCheck n && constructorCheck n) do
    throw (IO.userError "public-key observation backstop failed")
  unless (List.range 2400).all chainCheck do
    throw (IO.userError "public-key directed projection chains failed")
  IO.println "public-key backstop: 256 inputs and 2400 directed chain inputs passed"

end ExplainableCrypto.Helios.Symbolic.PublicKeyObservationExperiments
