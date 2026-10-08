import ExplainableCrypto.Helios.Symbolic.JointMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.MixedCompressionExperiments
open ExplainableCrypto.Testing Historical General

private def constructedLeaves : CiphertextAssembly 1 → List (Recipe 3)
  | .constructed k _ _ => [k]
  | .honest _ => []
  | .mul a b => constructedLeaves a ++ constructedLeaves b
private def compress (t : CiphertextAssembly 1) : Recipe 3 :=
  match t.group with
  | .mixed r p a => mixedCombinationRecipe r p a
  | _ => .const .bottom
private def view : Ground → Ground × Multiset Ground × AddSummary Ground
  | .ternary .penc k r p => (k,r.composeLeaves,p.addSyntaxSummary)
  | t => (t,0,.empty)

def singletonStrict (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 := .mul (.constructed (.var 0) (.name 40) (.const .zero)) (.honest (0,0))
  decide ((compress t).nodeCount < t.recipe.nodeCount)
def eraseIndexCost (_ : Nat) : Bool :=
  let a : Combination (HonestIndex 1) := .mul (.leaf (0,1)) (.leaf (1,1))
  decide ((combinationRecipe a).nodeCount = 2*a.indices.card+(a.indices.card-1))

def check (seed : Nat) : Bool :=
  let publicLeaf (i : Nat) : CiphertextAssembly 1 := .constructed
    (if (seed+i)%2=0 then .var 0 else .unary .fst (.binary .pair (.var 0) (.const .bottom)))
    (.name (40+i%3)) (if i%2=0 then .const .zero else .const .one)
  let honestLeaf (i : Nat) : CiphertextAssembly 1 := .honest
    (⟨i%2,by omega⟩,⟨(i/2)%2,by omega⟩)
  let t := (List.range (1+seed%4)).foldl (fun t i => .mul (publicLeaf i) t)
    ((List.range (seed/4%4)).foldl (fun t i => .mul t (honestLeaf (i+1))) (honestLeaf 0))
  let count := (constructedLeaves t).length
  let m := compress t
  (count == 1+seed%4) && decide (m.nodeCount+count ≤ t.recipe.nodeCount+1) &&
    (count<2 || decide (m.nodeCount<t.recipe.nodeCount)) &&
    [false,true].all (fun swap =>
      let φ := LocalRootSPOT.world swap
      decide (view (normalizeRaw (φ.eval t.recipe)) = view (normalizeRaw (φ.eval m))))

#eval campaign "strict mixed compression with one public constructor (negative control)" (∀ n : Nat, singletonStrict n = true) 1 true
#eval campaign "higher-index honest selector cost erased (negative control)" (∀ n : Nat, eraseIndexCost n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "mixed compression retains occurrence costs and both frame values" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "mixed compression backstop failed")
  IO.println "mixed compression backstop: 2048 inputs, one to four public and honest leaves, wrapped keys and both assignments"

end ExplainableCrypto.Helios.Symbolic.MixedCompressionExperiments
