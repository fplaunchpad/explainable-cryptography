import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedProofExperiments
open ExplainableCrypto.Testing Historical General

abbrev names := LocalRootSPOT.names
abbrev world (swap : Bool) := expandedFrame names swap LocalRootSPOT.left LocalRootSPOT.right []

def omitFourth (_ : Nat) : Bool :=
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  normalizeRaw ((world false).eval (.spk a a a (.name 40))) ==
    normalizeRaw ((world false).eval (.spk a a a (.name 41)))

def separateSingle (_ : Nat) : Bool :=
  let φ := expandedFrame ProofObservationSPOT.oneNames false ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight []
  normalizeRaw (φ.eval ((Term.var (expandedOld 1)).project 1)) !=
    normalizeRaw (φ.eval ((Term.var (expandedOld 1)).project 2))

def ignoreMinimum (_ : Nat) : Bool :=
  let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.spk (.name 40) (.name 41) (.name 42) (.name 43)) (.name 44))
  (match normalizeRaw ((world false).eval r) with | .spk _ _ _ _ => true | _ => false) &&
    (match r with | .spk _ _ _ _ => true | _ => false)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := world swap
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial j)
    let b : Recipe (ExpandedHandles 1) := .var (expandedResult j)
    let args := [a,b,.binary .partialDecrypt a b,.unary .pk a,.binary .compose a (.name (40+seed%5))]
    args.all (fun nonce =>
      let p : Recipe (ExpandedHandles 1) := .spk (.var (expandedOld 0)) nonce b (.name 60)
      normalizeRaw (φ.eval p) != normalizeRaw (componentProof names 0 (choice swap LocalRootSPOT.left LocalRootSPOT.right 0).value j) &&
      normalizeRaw (φ.eval p) != normalizeRaw (aggregateProof names 0 (choice swap LocalRootSPOT.left LocalRootSPOT.right 0).value) &&
      normalizeRaw (φ.eval p) != normalizeRaw (φ.eval (.spk (.var (expandedOld 0)) nonce b (.name 61))) &&
      normalizeRaw (φ.eval (.binary .dec a (keyCiphertext a (.name 70) p))) == normalizeRaw (φ.eval p)))

#eval campaign "proof comparison omits fourth binding (negative control)" (∀ n : Nat, omitFourth n = true) 1 true
#eval campaign "one-candidate component and aggregate proofs separated (negative control)" (∀ n : Nat, separateSingle n = true) 1 true
#eval campaign "nonminimum proof wrapper has constructor syntax (negative control)" (∀ n : Nat, ignoreMinimum n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "public proof nonces over expanded handles retain binding and successful E5"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded proof backstop failed")
  IO.println "expanded proof backstop: 2048 inputs, both candidates and swaps, nested published arguments"

end ExplainableCrypto.Helios.Symbolic.ExpandedProofExperiments
