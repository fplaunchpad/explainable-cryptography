import ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.PairObservationExperiments
open ExplainableCrypto.Testing Historical

private def tailRecipe (v : Fin 2) (k : Nat) : Recipe 3 := (Term.var v.succ).drop k

private def setup (seed : Nat) :=
  let n := seed % 5
  let ns := HistoricalFrameExperiments.generatedNames n
  let left := (BitCandidate.abstain n).substitution
  let right := (BitCandidate.selected (0 : Fin (n + 1))).substitution
  General.frame ns (seed / 5 % 2 == 1) left right

def tailCheck (seed : Nat) : Bool :=
  let count := fieldCount (seed % 5)
  let i : Fin 2 := ⟨seed / 10 % 2, Nat.mod_lt _ (by decide)⟩
  let j : Fin 2 := ⟨seed / 20 % 2, Nat.mod_lt _ (by decide)⟩
  let k := seed / 40 % count
  let l := seed / (40 * count) % count
  let φ := setup seed
  (normalizeRaw (φ.eval (tailRecipe i k)) == normalizeRaw (φ.eval (tailRecipe j l))) ==
    ((i == j) && (k == l))

def emptyTailMutation (seed : Nat) : Bool :=
  let φ := setup seed
  let count := fieldCount (seed % 5)
  normalizeRaw (φ.eval (tailRecipe 0 count)) != normalizeRaw (φ.eval (tailRecipe 1 count))

def mixedCheck (seed : Nat) : Bool :=
  let count := fieldCount (seed % 5)
  let t := tailRecipe (⟨seed / 10 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) (seed / 20 % count)
  let a := Term.unary .fst t
  let b := Term.unary .snd t
  let φ := setup seed
  let rebuilt := Term.binary .pair a b
  let changed := Term.binary .pair a (.const .bottom)
  let eq := fun r s => normalizeRaw (φ.eval r) == normalizeRaw (φ.eval s)
  eq rebuilt t &&
    ((eq changed t) == ((seed / 20 % count) == count - 1)) &&
    (decide (a.nodeCount + (Term.unary .fst t).nodeCount < rebuilt.nodeCount + t.nodeCount)) &&
    (decide (b.nodeCount + (Term.unary .snd t).nodeCount < rebuilt.nodeCount + t.nodeCount))

#eval campaign "tail voter identity without nonemptiness (negative control)"
  (∀ n : Nat, emptyTailMutation n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "fresh nonempty tails identify voter and offset" (∀ n : Nat, tailCheck n = true) seed
    campaign "constructed pairs compare both fields below original size" (∀ n : Nat, mixedCheck n = true) seed
  unless (List.range 256).all (fun n => tailCheck n && mixedCheck n) do
    throw (IO.userError "pair observation backstop failed")
  unless (List.range 6760).all tailCheck do
    throw (IO.userError "pair tail directed sweep failed")
  IO.println "pair observation backstop: 256 inputs and 6760 directed tail inputs passed"

end ExplainableCrypto.Helios.Symbolic.PairObservationExperiments
