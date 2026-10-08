import ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeyExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedShapeExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right

def dataShape : Ground → Bool
  | .binary .pair _ _ => true
  | .binary .partialDecrypt _ _ => true
  | .ternary .penc _ _ _ => true
  | _ => false

def allDecryptionsNumeric (_ : Nat) : Bool :=
  let key := tallyPartial names false left right [] 0
  let p : Ground := .binary .pair (.name 40) (.name 41)
  !dataShape (normalizeRaw (.binary .dec key (keyCiphertext key (.name 50) p)))

def ignoreBinding (_ : Nat) : Bool :=
  let out := normalizeRaw (.binary .dec (tallyPartial names false left right [] 0)
    (tallyCiphertext names false left right [] 1))
  decide (out.addSyntaxSummary = AddSummary.number 1)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let key := tallyPartial names swap left right [] j
    let c := tallyCiphertext names swap left right [] j
    let wrapped :=  (List.range (seed%5)).foldl (fun t _ => Term.unary .fst (.binary .pair t (.name 90))) c
    let out := normalizeRaw (.binary .dec key wrapped)
    !dataShape out && decide (out.addSyntaxSummary = AddSummary.number j.val) &&
    let p : Ground := match seed%3 with
      | 0 => .binary .pair (.name 40) (.name 41)
      | 1 => .ternary .penc (.name 40) (.name 41) (.const .one)
      | _ => .binary .partialDecrypt (.name 40) (.name 41)
    normalizeRaw (.binary .dec key (keyCiphertext key (.name 50) p)) == p &&
    dataShape (normalizeRaw (.binary .dec key (keyCiphertext key (.name 50) p))))

#eval campaign "all decryptions have numeric outputs (negative control)" (∀ n : Nat, allDecryptionsNumeric n = true) 1 true
#eval campaign "borrowed E6 ignores candidate binding (negative control)" (∀ n : Nat, ignoreBinding n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded E6 numeric outputs and E5 arbitrary data outputs" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded shape backstop failed")
  IO.println "expanded shape backstop: 2048 inputs, both candidates and swaps, zero through four wrappers, all three E5 data shapes"

end ExplainableCrypto.Helios.Symbolic.ExpandedShapeExperiments
