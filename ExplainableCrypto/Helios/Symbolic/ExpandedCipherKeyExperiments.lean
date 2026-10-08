import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeyExperiments
open ExplainableCrypto.Testing Historical General
abbrev world (swap : Bool) := expandedFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []

def isCipher : Ground → Bool
  | .ternary .penc _ _ _ => true
  | _ => false

def ignoreKeys (_ : Nat) : Bool :=
  isCipher (normalizeRaw (.binary .mul (.ternary .penc (.name 40) (.name 50) (.const .zero))
    (.ternary .penc (.name 41) (.name 51) (.const .one))))

def rawOnlyKeys (_ : Nat) : Bool :=
  let k : Ground := .unary .pk (.name 40)
  let w := Term.unary .fst (.binary .pair k (.name 41))
  decide (k=w) && isCipher (normalizeRaw (.binary .mul (.ternary .penc k (.name 50) (.const .zero))
    (.ternary .penc w (.name 51) (.const .one))))

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := world swap
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let key : Recipe (ExpandedHandles 1) := if seed%2=0 then .var (expandedOld 0)
      else .unary .pk (.binary .partialDecrypt (.var (expandedPartial j)) (.var (expandedResult j)))
    let wrapped := Term.unary .fst (.binary .pair key (.name 60))
    let a := Term.ternary .penc key (.name 40) (.const .zero)
    let b := Term.ternary .penc wrapped (.name 41) (.const .one)
    let product := (List.range (seed%5)).foldl (fun r _ => Term.binary .mul r a) (.binary .mul a b)
    isCipher (normalizeRaw (φ.eval product)) &&
    let honest := (Term.var (expandedOld (n := 1) 1)).project j.val
    let mixed := Term.binary .mul honest (.ternary .penc (.var (expandedOld 0)) (.name 50) (.const .zero))
    isCipher (normalizeRaw (φ.eval mixed)))

#eval campaign "different ciphertext keys fuse (negative control)" (∀ n : Nat, ignoreKeys n = true) 1 true
#eval campaign "raw equality required for ciphertext keys (negative control)" (∀ n : Nat, rawOnlyKeys n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded ciphertext shapes with nested and E-equal keys" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded ciphertext key backstop failed")
  IO.println "expanded ciphertext key backstop: 2048 inputs, both candidates and swaps, nested keys, honest leaves and repetitions"

end ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeyExperiments
