import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedCheckExperiments
open ExplainableCrypto.Testing Historical General
abbrev world (swap : Bool) := expandedFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []

def proofCheck (key nonce : Recipe (ExpandedHandles 1)) (bit : Constant) : Recipe (ExpandedHandles 1) :=
  let cipher := Term.ternary .penc key nonce (.const bit)
  .ternary .checkspk key cipher (.spk key nonce (.const bit) cipher)

def successfulInjective (_ : Nat) : Bool :=
  normalizeRaw ((world false).eval (proofCheck (.name 40) (.name 41) .zero)) !=
    normalizeRaw ((world false).eval (proofCheck (.name 42) (.name 43) .one))

def ignoreMinimum (_ : Nat) : Bool :=
  let check : Recipe (ExpandedHandles 1) := .ternary .checkspk (.name 40) (.name 41) (.name 42)
  let r := Term.unary .fst (.binary .pair check (.name 43))
  normalizeRaw ((world false).eval r) == (world false).eval check &&
    (match r with | .ternary .checkspk _ _ _ => true | _ => false)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := world swap
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial j)
    let nonce := Term.binary .partialDecrypt a (.var (expandedResult j))
    let key := Term.unary .pk a
    [Constant.zero,Constant.one].all (fun bit =>
      let cipher := Term.ternary .penc key nonce (.const bit)
      let bad := Term.spk key nonce (.const bit) (.name (40+seed%7))
      normalizeRaw (φ.eval (proofCheck key nonce bit)) == .const .ok &&
      (match normalizeRaw (φ.eval (.ternary .checkspk key cipher bad)) with | .ternary .checkspk _ _ _ => true | _ => false)))

#eval campaign "successful proof checks injective in arguments (negative control)" (∀ n : Nat, successfulInjective n = true) 1 true
#eval campaign "nonminimum stuck-check wrapper has check syntax (negative control)" (∀ n : Nat, ignoreMinimum n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded proof checks retain both success rules and fourth binding" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded check backstop failed")
  IO.println "expanded check backstop: 2048 inputs, both candidates and swaps, both bits and nested published arguments"

end ExplainableCrypto.Helios.Symbolic.ExpandedCheckExperiments
