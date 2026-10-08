import ExplainableCrypto.Helios.Symbolic.HistoricalFrames
import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Testing.Plausible

namespace ExplainableCrypto.Helios.Symbolic.HistoricalFrameExperiments
open ExplainableCrypto.Testing Historical

def generatedNames (n : Nat) : Names n :=
  ⟨0, 1, fun i j => 2 + i.val * (n + 1) + j.val⟩

def frameCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let ns := generatedNames n
  let a : Fin (n + 1) := ⟨seed % (n + 1), Nat.mod_lt _ (by omega)⟩
  let b : Fin (n + 1) := ⟨(seed + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩
  [false, true].all fun swap =>
    (List.finRange 2).all fun i =>
      let c := choice swap a b i
      let fields := ballotFields ns i c
      let bits := (List.finRange (n + 1)).map (vote c)
      (fields.length == 2 * (n + 1) + 1) &&
      (bits.count (.const .one) == 1) &&
      (bits.count (.const .zero) == n) &&
      ((List.finRange (n + 1)).all fun j =>
        normalizeRaw ((ballot ns i c).project j.val) == normalizeRaw (ciphertext ns i c j)) &&
      ((frame ns swap a b).value ⟨i.val + 1, by omega⟩ == ballot ns i c) &&
      (c == (if (i.val == 0) == !swap then a else b))

#eval campaign "two fields per candidate suffice (negative control)"
  (∀ n : Nat, (ballotFields (generatedNames n) 0 0).length = 2 * (n + 1)) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "historical frame counts, one-hot votes, swaps and projections"
      (∀ n : Nat, frameCheck n = true) seed
  unless (List.range 256).all frameCheck do
    throw (IO.userError "historical frame backstop failed")
  IO.println "historical frame backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.HistoricalFrameExperiments
