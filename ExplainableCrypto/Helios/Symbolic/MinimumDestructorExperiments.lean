import ExplainableCrypto.Helios.Symbolic.AtomicObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.MinimumDestructorExperiments
open ExplainableCrypto.Testing Historical

private def setup (seed : Nat) :=
  let n := seed % 5
  General.frame (HistoricalFrameExperiments.generatedNames n) (seed / 5 % 2 == 1)
    (BitCandidate.abstain n).substitution (BitCandidate.selected (0 : Fin (n + 1))).substitution
private def isPair : Term V → Bool | .binary .pair _ _ => true | _ => false
private def isCipher : Term V → Bool | .ternary .penc _ _ _ => true | _ => false
private def isProof : Term V → Bool | .spk _ _ _ _ => true | _ => false

def projectionCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let count := fieldCount n
  let k := seed / 20 % count
  let i : Fin 2 := ⟨seed / 10 % 2, Nat.mod_lt _ (by decide)⟩
  let a : Recipe 3 := (Term.var i.succ).drop k
  let φ := setup seed
  let x := normalizeRaw (φ.eval (.unary .fst a))
  let y := normalizeRaw (φ.eval (.unary .snd a))
  isPair (normalizeRaw (φ.eval a)) &&
    (if k < n + 1 then isCipher x else isProof x) &&
    (if k + 1 = count then y == .const .bottom else isPair y)

def observerCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let j := seed / 10 % (n + 1)
  let φ := setup seed
  let cipher : Recipe 3 := (Term.var 1).project j
  let good : Recipe 3 := .ternary .checkspk (.var 0) cipher ((Term.var 1).project (n + 1 + j))
  let bad : Recipe 3 := .ternary .checkspk (.var 0) cipher ((Term.var 2).project (n + 1 + j))
  (normalizeRaw (φ.eval good) == .const .ok) &&
    (normalizeRaw (φ.eval bad) != .const .ok) &&
    decide (good.nodeCount + 1 < good.nodeCount + bad.nodeCount) &&
    decide (bad.nodeCount + 1 < good.nodeCount + bad.nodeCount)

def ignoredProofField (seed : Nat) : Bool :=
  let a : Ground := .ternary .checkspk (.name 40) (.name 41) (.name (50 + seed % 3))
  let b : Ground := .ternary .checkspk (.name 40) (.name 41) (.name (60 + seed % 3))
  normalizeRaw a == normalizeRaw b

def omittedMinimum (seed : Nat) : Bool :=
  let φ := setup seed
  let r : Recipe 3 := .unary .fst (.binary .pair (.var 0) (.const .bottom))
  let x := normalizeRaw (φ.eval r)
  isPair x || isCipher x || isProof x

#eval campaign "stuck checks ignore their proof field (negative control)"
  (∀ n : Nat, ignoredProofField n = true) 1 true
#eval campaign "successful projection classification omits minimum size (negative control)"
  (∀ n : Nat, omittedMinimum n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "honest projections retain field kinds and terminal boundary" (∀ n : Nat, projectionCheck n = true) seed
    campaign "whole-check ok probes distinguish matching and wrong proofs below bound"
      (∀ n : Nat, observerCheck n = true) seed
  unless (List.range 256).all (fun n => projectionCheck n && observerCheck n) do
    throw (IO.userError "minimum destructor observation backstop failed")
  IO.println "minimum destructor observation backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.MinimumDestructorExperiments
