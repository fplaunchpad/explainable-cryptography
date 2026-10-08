import ExplainableCrypto.Helios.Symbolic.ExpandedStuckExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedCompositionExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right

def leaves : Ground → List Ground
  | .binary .compose a b => leaves a ++ leaves b
  | t => [t]

def eraseDuplicates (_ : Nat) : Bool :=
  let t : Ground := .binary .compose (.name 40) (.name 40)
  decide ((leaves t).Perm (leaves t).eraseDups)

def hiddenComposition (_ : Nat) : Bool :=
  let t : Ground := .unary .fst (.binary .pair (.binary .compose (.name 40) (.name 41)) (.name 50))
  decide ((leaves t).length = (leaves (normalizeRaw t)).length)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := expandedFrame names swap left right []
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let a : Recipe (ExpandedHandles 1) := match seed%4 with
      | 0 => .var (expandedPartial j)
      | 1 => .var (expandedResult j)
      | 2 => .unary .pk (.var (expandedResult j))
      | _ => .unary .fst (.var (expandedPartial j))
    let b : Recipe (ExpandedHandles 1) := .name (40+seed%5)
    let x := Term.binary .compose a (.binary .compose b a)
    let y := Term.binary .compose (.binary .compose a a) b
    let va := normalizeRaw (φ.eval a)
    let vb := normalizeRaw (φ.eval b)
    decide ((leaves (normalizeRaw (φ.eval x))).Perm [va,vb,va]) &&
    decide ((leaves (normalizeRaw (φ.eval x))).Perm (leaves (normalizeRaw (φ.eval y)))) &&
    decide ((leaves (normalizeRaw (φ.eval x))).length = 3) &&
    (match normalizeRaw (φ.eval a) with | .binary .compose _ _ => false | _ => true) &&
    normalizeRaw (φ.eval (.binary .dec (.var (expandedPartial j))
      (keyCiphertext (.var (expandedPartial j)) (.name 50) x))) == normalizeRaw (φ.eval x))

#eval campaign "composition erases repeated factors (negative control)" (∀ n : Nat, eraseDuplicates n = true) 1 true
#eval campaign "raw leaves always remain semantic atoms (negative control)" (∀ n : Nat, hiddenComposition n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded composition factors retain multiplicity and published-value atoms" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded composition backstop failed")
  IO.println "expanded composition backstop: 2048 inputs, both candidates and swaps, partial/result/key/stuck leaves, repeated factors and E5 wrappers"

end ExplainableCrypto.Helios.Symbolic.ExpandedCompositionExperiments
