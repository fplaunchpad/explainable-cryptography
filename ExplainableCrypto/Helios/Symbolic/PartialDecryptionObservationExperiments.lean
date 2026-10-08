import ExplainableCrypto.Helios.Symbolic.PublicKeyObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationExperiments
open ExplainableCrypto.Testing Historical

private def chain : Nat → Nat → Recipe 3
  | 0, seed => .var ⟨seed % 3, Nat.mod_lt _ (by decide)⟩
  | d + 1, seed => .unary (if seed % 2 = 0 then .fst else .snd) (chain d (seed / 2))
private def isPartial : Term V → Bool
  | .binary .partialDecrypt _ _ => true
  | _ => false

private def generatedFrame (seed : Nat) :=
  let n := seed % 5
  General.frame (HistoricalFrameExperiments.generatedNames n) (seed / 5 % 2 == 1)
    (BitCandidate.abstain n).substitution (BitCandidate.selected (0 : Fin (n + 1))).substitution

def chainCheck (seed : Nat) : Bool :=
  !isPartial (normalizeRaw ((generatedFrame seed).eval (chain (seed / 10 % 5) (seed / 50))))

def constructorCheck (seed : Nat) : Bool :=
  let a : Recipe 3 := .name (40 + seed % 3)
  let b : Recipe 3 := .name (50 + seed % 3)
  let reveal := fun t => Term.unary .fst (.binary .pair t (.const .bottom))
  let φ := generatedFrame seed
  let x := normalizeRaw (φ.eval (.binary .partialDecrypt (reveal a) (reveal b)))
  let expected : Ground := .binary .partialDecrypt (.name (40 + seed % 3)) (.name (50 + seed % 3))
  (x == expected) && (x != .binary .partialDecrypt (.name (50 + seed % 3)) (.name (40 + seed % 3)))

def commutationCheck (seed : Nat) : Bool :=
  let a : Ground := .name (40 + seed % 3)
  let b : Ground := .name (50 + seed % 3)
  normalizeRaw (.binary .partialDecrypt a b) == normalizeRaw (.binary .partialDecrypt b a)

def nonminimumOriginCheck (seed : Nat) : Bool :=
  let r : Recipe 3 := .unary .fst (.binary .pair
    (.binary .partialDecrypt (.name (40 + seed % 3)) (.name 50)) (.const .bottom))
  !isPartial (normalizeRaw ((generatedFrame seed).eval r)) || isPartial r

#eval campaign "partial-decryption arguments commute (negative control)"
  (∀ n : Nat, commutationCheck n = true) 1 true
#eval campaign "partial-decryption origins omit minimum size (negative control)"
  (∀ n : Nat, nonminimumOriginCheck n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "initial frame chains expose no partial-decryption values" (∀ n : Nat, chainCheck n = true) seed
    campaign "partial-decryption construction retains ordered independently specified fields"
      (∀ n : Nat, constructorCheck n = true) seed
  unless (List.range 256).all (fun n => chainCheck n && constructorCheck n) do
    throw (IO.userError "partial-decryption observation backstop failed")
  unless (List.range 2400).all chainCheck do
    throw (IO.userError "partial-decryption directed chains failed")
  IO.println "partial-decryption backstop: 256 inputs and 2400 directed chain inputs passed"

end ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationExperiments
