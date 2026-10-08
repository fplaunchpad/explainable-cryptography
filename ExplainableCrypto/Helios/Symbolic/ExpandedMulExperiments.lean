import ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedMulExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private def isMul : Ground → Bool
  | .binary .mul _ _ => true
  | _ => false
private def cipher (nonce : Nat) : Recipe (ExpandedHandles 1) :=
  keyCiphertext (.var (expandedPartial 0)) (.name nonce) (.name 80)

def unfusedMutation (_ : Nat) : Bool :=
  let r := Term.binary .mul (.binary .mul (cipher 40) (cipher 41)) (.var (expandedResult 0))
  decide (r.mulLeaves.card = (normalizeRaw ((world false).eval r)).mulLeaves.card)

def hiddenMutation (_ : Nat) : Bool :=
  let r : Recipe (ExpandedHandles 1) := .unary .fst
    (.binary .pair (.binary .mul (.var (expandedPartial 0)) (.var (expandedResult 0))) (.name 50))
  decide (r.mulLeaves.card = (normalizeRaw ((world false).eval r)).mulLeaves.card)

def fusedHeadMutation (_ : Nat) : Bool :=
  isMul (normalizeRaw ((world false).eval (.binary .mul (cipher 40) (cipher 41))))

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let count := 1+seed%5
    let marker : Recipe (ExpandedHandles 1) := .var (expandedPartial j)
    let product := (List.range count).foldl (fun r _ => .binary .mul r marker) (.var (expandedResult j))
    let withFusion := Term.binary .mul (.binary .mul (cipher (40+seed%7)) (cipher (50+seed%7))) product
    let normalized := normalizeRaw ((world swap).eval withFusion)
    decide (withFusion.mulLeaves.card = count+3) &&
    decide (normalized.mulLeaves.card = count+2) && isMul normalized &&
    !isMul (normalizeRaw ((world swap).eval (.var (expandedResult j)))) &&
    !isMul (normalizeRaw ((world swap).eval marker)) &&
    decide ((normalizeRaw ((world swap).eval (.unary .fst (.binary .pair withFusion (.name 60))))).mulLeaves.card = count+2))

#eval campaign "unfused published-product leaves (negative control)" (∀ n : Nat, unfusedMutation n = true) 1 true
#eval campaign "hidden product preserves raw leaf count (negative control)" (∀ n : Nat, hiddenMutation n = true) 1 true
#eval campaign "fused ciphertext retains multiplication head (negative control)" (∀ n : Nat, fusedHeadMutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded multiplication retains numeric/partial factors and grouped ciphertext fusion" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded multiplication backstop failed")
  IO.println "expanded multiplication backstop: 2048 inputs, both candidates and swaps, one through five repeated partial factors, result handles, ciphertext fusion and projection wrappers"

end ExplainableCrypto.Helios.Symbolic.ExpandedMulExperiments
