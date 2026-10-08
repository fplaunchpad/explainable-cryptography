import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.BaseStructure

namespace ExplainableCrypto.Helios.Symbolic.FullStructureExperiments
open ExplainableCrypto.Testing RewriteExperiments

def passiveCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 7)
  let c := generatedTerm (n % 4) (n + 11)
  let d := generatedTerm (n % 4) (n + 19)
  (normalizeRaw (.ternary .penc a b c) == .ternary .penc (normalizeRaw a) (normalizeRaw b) (normalizeRaw c)) &&
  (normalizeRaw (.spk a b c d) == .spk (normalizeRaw a) (normalizeRaw b) (normalizeRaw c) (normalizeRaw d)) &&
  ([Binary.pair, .partialDecrypt].all fun f =>
    normalizeRaw (.binary f a b) == .binary f (normalizeRaw a) (normalizeRaw b))

#eval campaign "all full-E equations preserve raw heads (negative control)"
  (∀ n : Nat, (normalizeRaw (.binary .dec (.name 0)
    (.ternary .penc (.unary .pk (.name 0)) (.name 1) (.name n)) : Term Nat)).headTag = .binary .dec) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "passive constructors preserve independently reduced components"
      (∀ n : Nat, passiveCheck n = true) seed
  unless (List.range 256).all passiveCheck do
    throw (IO.userError "passive constructor backstop failed")
  IO.println "passive constructor backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.FullStructureExperiments
