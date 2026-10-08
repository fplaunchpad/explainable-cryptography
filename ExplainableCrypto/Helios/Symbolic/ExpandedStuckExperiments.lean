import ExplainableCrypto.Helios.Symbolic.ExpandedShapeExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedStuckExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right

def forgetSelector (_ : Nat) : Bool :=
  normalizeRaw (Term.unary .fst (.name 40) : Ground) == normalizeRaw (.unary .snd (.name 40))
def stuckHeadWithoutMinimum (_ : Nat) : Bool :=
  let r : Recipe 1 := .unary .fst (.binary .pair (.binary .dec (.name 40) (.name 41)) (.name 50))
  decide (r.headTag = .binary .dec)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := expandedFrame names swap left right []
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let arg : Recipe (ExpandedHandles 1) := if seed%2=0 then .var (expandedPartial j)
      else .unary .pk (.var (expandedResult j))
    let u := Term.unary .fst arg
    let v := Term.unary .snd arg
    let d := Term.binary .dec arg (.name (40+seed%5))
    (match normalizeRaw (φ.eval u) with | .unary .fst _ => true | _ => false) &&
    (match normalizeRaw (φ.eval v) with | .unary .snd _ => true | _ => false) &&
    (match normalizeRaw (φ.eval d) with | .binary .dec _ _ => true | _ => false) &&
    let wrapped := Term.unary .fst (.binary .pair d (.name 90))
    normalizeRaw (φ.eval wrapped) == normalizeRaw (φ.eval d) &&
    normalizeRaw (φ.eval (.unary .fst (.binary .pair u v))) == normalizeRaw (φ.eval u) &&
    normalizeRaw (φ.eval (.binary .dec arg (keyCiphertext arg (.name 50) v))) == normalizeRaw (φ.eval v))

#eval campaign "stuck projections forget selector (negative control)" (∀ n : Nat, forgetSelector n = true) 1 true
#eval campaign "nonminimum stuck value forces raw head (negative control)" (∀ n : Nat, stuckHeadWithoutMinimum n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded stuck selectors and decryption retain raw origins versus successful wrappers" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded stuck backstop failed")
  IO.println "expanded stuck backstop: 2048 inputs, both candidates and swaps, partial/result arguments, both selectors and successful wrappers"

end ExplainableCrypto.Helios.Symbolic.ExpandedStuckExperiments
