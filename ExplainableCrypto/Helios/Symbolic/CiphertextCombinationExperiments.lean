import ExplainableCrypto.Helios.Symbolic.CiphertextCombinations
import ExplainableCrypto.Helios.Symbolic.StaticObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.CiphertextCombinationExperiments
open ExplainableCrypto.Testing Historical

private def nonceLeaves : Ground → List Nat
  | .name n => [n]
  | .binary .compose a b => nonceLeaves a ++ nonceLeaves b
  | _ => []

private def candidate (n : Nat) (abstain : Bool) (chosen : Fin (n + 1)) : BitCandidate n :=
  if abstain then .abstain n else .selected chosen

def combinationCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let mode := seed / 5 % 4
  let swap := seed / 20 % 2 == 1
  let leftZero := mode % 2 == 0
  let rightZero := mode / 2 == 0
  let leftPos : Fin (n + 1) := ⟨seed / 40 % (n + 1), Nat.mod_lt _ (by omega)⟩
  let rightPos : Fin (n + 1) := ⟨seed / 80 % (n + 1), Nat.mod_lt _ (by omega)⟩
  let ns := HistoricalFrameExperiments.generatedNames n
  let φ := General.frame ns swap (candidate n leftZero leftPos).substitution
    (candidate n rightZero rightPos).substitution
  let index := fun offset => ((⟨(seed / 40 + offset % 2) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2),
    (⟨(seed / 80 + offset) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)))
  let a := index 0
  let b := index 1
  let c := index 2
  let t := Combination.mul (.mul (.leaf a) (.leaf b)) (.mul (.leaf a) (.leaf c))
  let u := Combination.mul (.leaf c) (.mul (.leaf a) (.mul (.leaf b) (.leaf a)))
  let v := Combination.mul (.mul (.leaf a) (.leaf b)) (.leaf c)
  let xs := [a, b, a, c]
  let count := (xs.filter fun i =>
    let useRight := if i.1.val = 0 then swap else !swap
    let abstain := if useRight then rightZero else leftZero
    let pos := if useRight then rightPos else leftPos
    !abstain && i.2 == pos).length
  match normalizeRaw (φ.eval (General.combinationRecipe t)), normalizeRaw (φ.eval (General.combinationRecipe u)),
      normalizeRaw (φ.eval (General.combinationRecipe v)) with
  | .ternary .penc k r m, .ternary .penc k' r' m', .ternary .penc _ r'' _ =>
    (k == .unary .pk (.name 0)) && (k == k') &&
      decide ((nonceLeaves r).Perm (xs.map fun i => 2 + i.1.val * (n + 1) + i.2.val)) &&
      decide ((nonceLeaves r).Perm (nonceLeaves r')) &&
      decide (¬ (nonceLeaves r).Perm (nonceLeaves r'')) &&
      (m.addSummary.atoms.card == 0) && (m.addSummary.numeric == some count) &&
      (m'.addSummary.numeric == some count)
  | _, _, _ => false

#eval campaign "nonce sets forget multiplicity (negative control)"
  (∀ n : Nat, decide (([n] : List Nat).Perm [n, n]) = true) 1 true
#eval campaign "colliding nonce labels determine indices (negative control)"
  (∀ n : Nat, decide (([20] : List Nat).Perm [20] ↔ ([n] : List Nat).Perm [n + 1]) = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "honest ciphertext combinations retain nonce multiplicities"
      (∀ n : Nat, combinationCheck n = true) seed
  unless (List.range 256).all combinationCheck do
    throw (IO.userError "ciphertext-combination backstop failed")
  IO.println "ciphertext-combination backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.CiphertextCombinationExperiments
