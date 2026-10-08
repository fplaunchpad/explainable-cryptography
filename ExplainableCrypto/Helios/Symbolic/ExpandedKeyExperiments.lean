import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedKeyExperiments
open ExplainableCrypto.Testing Historical General

def ignoreMinimum (_ : Nat) : Bool :=
  let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedOld 0)) (.name 90))
  let φ := expandedFrame LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right []
  normalizeRaw (φ.eval r) == publicKey LocalRootSPOT.names &&
    (match r with | .var _ | .unary .pk _ => true | _ => false)

def omitSecretRestriction (_ : Nat) : Bool :=
  let φ := expandedFrame LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right []
  normalizeRaw (φ.eval (.unary .pk (.name LocalRootSPOT.names.secretKey))) !=
    normalizeRaw (φ.value (expandedOld 0))

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := expandedFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let part : Recipe (ExpandedHandles 1) := .var (expandedPartial j)
    let result : Recipe (ExpandedHandles 1) := .var (expandedResult j)
    let args := [part, result, .binary .partialDecrypt part result,
      .binary .pair part (.name (40+seed%5)), .unary .pk part,
      .binary .compose part (.name (50+seed%7))]
    args.all (fun a =>
      normalizeRaw (φ.eval (.unary .pk a)) != normalizeRaw (φ.value (expandedOld 0)) &&
      args.all (fun b =>
        decide ((normalizeRaw (φ.eval (.unary .pk a)) == normalizeRaw (φ.eval (.unary .pk b))) =
          (normalizeRaw (φ.eval a) == normalizeRaw (φ.eval b))))))

#eval campaign "nonminimum key wrappers must have minimum syntax (negative control)"
  (∀ n : Nat, ignoreMinimum n = true) 1 true
#eval campaign "constructed election key differs without secret restriction (negative control)"
  (∀ n : Nat, omitSecretRestriction n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "constructed keys over published values preserve argument comparisons"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded key backstop failed")
  IO.println "expanded key backstop: 2048 inputs, both candidates and swaps, nested public key arguments"

end ExplainableCrypto.Helios.Symbolic.ExpandedKeyExperiments
