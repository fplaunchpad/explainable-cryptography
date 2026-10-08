import ExplainableCrypto.Helios.Symbolic.ExpandedHonestExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedMixedExperiments
open ExplainableCrypto.Testing Historical General
abbrev world := ExpandedConstructedExperiments.world
private def compress (t : CiphertextAssembly 1 (ExpandedHandles 1)) : Recipe (ExpandedHandles 1) :=
  match t.group with
  | .mixed r p a => .binary .mul (.ternary .penc (.var (expandedOld 0)) r p)
      ((combinationRecipe a).subst (fun i => .var (expandedOld i)))
  | _ => .const .bottom
private def tree (seed : Nat) : CiphertextAssembly 1 (ExpandedHandles 1) :=
  let leaf (i : Nat) : CiphertextAssembly 1 (ExpandedHandles 1) :=
    .constructed (if i%2=0 then .var (expandedOld 0)
      else .unary .fst (.binary .pair (.var (expandedOld 0)) (.const .bottom)))
      (if i%2=0 then .var (expandedPartial 0) else .name (40+i%3))
      (.var (expandedResult ⟨i%2,by omega⟩))
  (List.range (2+seed%5)).foldl
    (fun t i => .mul (leaf i) (.mul t (.honest (⟨(i+seed)%2,by omega⟩,⟨(i/2+seed)%2,by omega⟩))))
    (.honest (0,0))
private def view : Ground → Ground × Multiset Ground × AddSummary Ground
  | .ternary .penc k r p => (k,r.composeLeaves,p.addSyntaxSummary)
  | t => (t,0,.empty)

def singleton_strict_mutation (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 (ExpandedHandles 1) :=
    .mul (.constructed (.var (expandedOld 0)) (.name 40) (.const .zero)) (.honest (0,0))
  decide ((compress t).nodeCount < (t.recipeWith expandedOld).nodeCount)
def erase_honest_duplicate_mutation (_ : Nat) : Bool :=
  let a : CiphertextAssembly 1 (ExpandedHandles 1) :=
    .mul (.constructed (.var (expandedOld 0)) (.name 40) (.const .zero)) (.honest (0,0))
  decide (view (normalizeRaw ((world false).eval ((a.mul (.honest (0,0))).recipeWith expandedOld))) =
    view (normalizeRaw ((world false).eval (a.recipeWith expandedOld))))
def incoherent_key_mutation (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 (ExpandedHandles 1) :=
    .mul (.constructed (.var (expandedPartial 0)) (.name 40) (.const .zero)) (.honest (0,0))
  decide (view (normalizeRaw ((world false).eval (t.recipeWith expandedOld))) =
    view (normalizeRaw ((world false).eval (compress t))))
def check (seed : Nat) : Bool :=
  let t := tree seed
  decide ((compress t).nodeCount < (t.recipeWith expandedOld).nodeCount) &&
    [false,true].all (fun swap => decide
      (view (normalizeRaw ((world swap).eval (t.recipeWith expandedOld))) =
        view (normalizeRaw ((world swap).eval (compress t)))))

#eval campaign "one mixed constructor compresses strictly (negative control)" (∀ n : Nat, singleton_strict_mutation n = true) 1 true
#eval campaign "mixed honest duplicate erased (negative control)" (∀ n : Nat, erase_honest_duplicate_mutation n = true) 1 true
#eval campaign "mixed public partial key fuses with election key (negative control)" (∀ n : Nat, incoherent_key_mutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded mixed compression preserves occurrences and strict size" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded mixed compression backstop failed")
  IO.println "expanded mixed compression backstop: 2048 inputs, both swaps, two through six constructors, three through seven honest selectors, published components and delayed keys"

end ExplainableCrypto.Helios.Symbolic.ExpandedMixedExperiments
