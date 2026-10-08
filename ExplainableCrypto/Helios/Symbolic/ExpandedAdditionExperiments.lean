import ExplainableCrypto.Helios.Symbolic.ExpandedCompositionExperiments
import ExplainableCrypto.Helios.Symbolic.SharedTallySPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionSummary

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAdditionExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right

def resultIsAtom (_ : Nat) : Bool :=
  let φ := expandedFrame names false left right []
  decide ((normalizeRaw (φ.eval (.var (expandedResult 0)))).addSyntaxSummary.atoms.card = 1)

def erasePublishedZero (_ : Nat) : Bool :=
  let φ := expandedFrame names false left right []
  let r : Recipe (ExpandedHandles 1) := .binary .add (.name 40) (.var (expandedResult 0))
  decide ((normalizeRaw (φ.eval r)).addSyntaxSummary.numeric = none)

def literalCostForResult (_ : Nat) : Bool :=
  let φ := expandedFrame SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
  let r : Recipe (ExpandedHandles 0) := .var (expandedResult 0)
  decide ((normalizeRaw (φ.eval r)).addSyntaxSummary = AddSummary.number 2) &&
    decide (numericRecipeCost (some 2) ≤ r.nodeCount + 1)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := expandedFrame names swap left right []
    let j : Fin 2 := ⟨seed%2,by omega⟩
    let count := seed%5
    let r : Recipe (ExpandedHandles 1) := (List.range count).foldl
      (fun r _ => .binary .add r (.var (expandedResult j))) (.var (expandedResult 0))
    let withAtoms := Term.binary .add (.name 40) (.binary .add r (.name 40))
    let expected : AddSummary Ground := ⟨{.name 40,.name 40},some (count*j.val)⟩
    let expectedRecipe : AddSummary (Recipe (ExpandedHandles 1)) := ⟨{.name 40,.name 40},some (count*j.val)⟩
    decide (withAtoms.addNumericSummary (expandedNumericHandles (fun j : Fin 2 => j.val)) = expectedRecipe) &&
    decide ((normalizeRaw (φ.eval withAtoms)).addSyntaxSummary = expected) &&
    let delayed := Term.unary .fst (.binary .pair withAtoms (.name 50))
    decide ((normalizeRaw (φ.eval delayed)).addSyntaxSummary = expected))

#eval campaign "published numeric result remains an atom (negative control)" (∀ n : Nat, resultIsAtom n = true) 1 true
#eval campaign "published zero may be erased (negative control)" (∀ n : Nat, erasePublishedZero n = true) 1 true
#eval campaign "literal numeric costs bound published result (negative control)" (∀ n : Nat, literalCostForResult n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "published numeric leaves retain zero presence and repeated atoms" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded addition backstop failed")
  IO.println "expanded addition backstop: 2048 inputs, both candidates and swaps, zero through four numeric slots, repeated atoms and wrappers"

end ExplainableCrypto.Helios.Symbolic.ExpandedAdditionExperiments
