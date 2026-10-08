import ExplainableCrypto.Helios.Symbolic.HistoricalFrameExperiments
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT

namespace ExplainableCrypto.Helios.Symbolic.HistoricalSelectorExperiments
open ExplainableCrypto.Testing Historical

def selector (i : Nat) : Recipe 3 := (Term.var 1).project i

def singleSelector : Recipe 3 → Bool
  | .unary .fst (.var _) | .unary .snd (.var _) => true
  | _ => false

def selectorCheck (seed : Nat) : Bool :=
  let j : Fin 2 := ⟨seed % 2, Nat.mod_lt _ (by decide)⟩
  let fr := frame HistoricalFrameSPOT.names false 0 1
  normalizeRaw (fr.eval (selector j.val)) == ciphertext HistoricalFrameSPOT.names 0 0 j

#eval campaign "every indexed tuple projection is one binary selector (negative control)"
  (∀ n : Nat, singleSelector (selector (n % 2)) = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "first and second historical ciphertext selector outputs"
      (∀ n : Nat, selectorCheck n = true) seed
  unless (List.range 256).all selectorCheck do
    throw (IO.userError "historical selector backstop failed")
  IO.println "historical selector backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.HistoricalSelectorExperiments
