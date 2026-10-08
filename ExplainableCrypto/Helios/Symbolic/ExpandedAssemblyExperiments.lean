import ExplainableCrypto.Helios.Symbolic.AssemblyHandleSyntax
import ExplainableCrypto.Helios.Symbolic.ExpandedGroupExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAssemblyExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private def isCipher : Ground → Bool
  | .ternary .penc _ _ _ => true
  | _ => false
private def key : Recipe (ExpandedHandles 1) := .var (expandedOld 0)
private def delayedKey : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair key (.name 40))

def wrongKeyMutation (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 (ExpandedHandles 1) := .mul
    (.constructed (.name 40) (.name 41) (.const .zero)) (.honest (0,0))
  isCipher (normalizeRaw ((world false).eval (t.recipeWith expandedOld)))

def partialSelectorMutation (_ : Nat) : Bool :=
  isCipher (normalizeRaw ((world false).eval (.unary .fst (.var (expandedPartial 0)))))

def keySizeMutation (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed delayedKey (.name 40) (.const .zero)
  decide ((t.keyRecipeWith expandedOld).nodeCount = 1)

def assembly (seed : Nat) : CiphertextAssembly 1 (ExpandedHandles 1) :=
  let initial : CiphertextAssembly 1 (ExpandedHandles 1) := .mul
    (.constructed delayedKey (.var (expandedPartial 0)) (.var (expandedResult 1))) (.honest (0,0))
  (List.range (seed%5)).foldl (fun t i => .mul t
    (if (seed+i)%2 = 0 then .constructed key (.name (40+i)) (.var (expandedResult ⟨i%2,by omega⟩))
     else .honest (⟨i%2,by omega⟩,⟨(seed+i)%2,by omega⟩))) initial

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let t := assembly seed
    let φ := world swap
    let r := t.recipeWith expandedOld
    let expectedNonce := normalizeRaw (t.group.nonce names φ)
    let expectedMessage := normalizeRaw (t.group.message φ swap left right)
    let expectedKey := normalizeRaw (φ.eval (t.keyRecipeWith expandedOld))
    decide (t.group.budget ≤ r.nodeCount) && decide ((t.keyRecipeWith expandedOld).nodeCount < r.nodeCount) &&
    match normalizeRaw (φ.eval r) with
    | .ternary .penc k nonce message =>
      decide (k = expectedKey) && decide (nonce.composeLeaves = expectedNonce.composeLeaves) &&
      decide (message.addSyntaxSummary = expectedMessage.addSyntaxSummary)
    | _ => false)

#eval campaign "incoherent keys form a ciphertext (negative control)" (∀ n : Nat, wrongKeyMutation n = true) 1 true
#eval campaign "published partial selector is a ciphertext leaf (negative control)" (∀ n : Nat, partialSelectorMutation n = true) 1 true
#eval campaign "every selected key costs one node (negative control)" (∀ n : Nat, keySizeMutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded ciphertext assemblies preserve grouped values and original-size bounds" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded assembly backstop failed")
  IO.println "expanded assembly backstop: 2048 inputs, both swaps, mixed constructed/honest trees, published partial/result subrecipes, nonliteral keys and zero through four extra leaves"

end ExplainableCrypto.Helios.Symbolic.ExpandedAssemblyExperiments
