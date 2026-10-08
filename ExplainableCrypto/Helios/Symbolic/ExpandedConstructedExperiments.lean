import ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedConstructedExperiments
open ExplainableCrypto.Testing Historical General
abbrev world := ExpandedMulMinimumExperiments.world
private def compress (t : CiphertextAssembly 1 (ExpandedHandles 1)) : Recipe (ExpandedHandles 1) :=
  match t.group with
  | .constructed r p => .ternary .penc (t.keyRecipeWith expandedOld) r p
  | _ => .const .bottom
private def key (seed : Nat) : Recipe (ExpandedHandles 1) :=
  if seed%2=0 then .var (expandedPartial 0)
  else .unary .pk (.binary .pair (.var (expandedPartial 1)) (.var (expandedResult 1)))
private def tree (seed : Nat) : CiphertextAssembly 1 (ExpandedHandles 1) :=
  let leaf (i : Nat) : CiphertextAssembly 1 (ExpandedHandles 1) :=
    .constructed (if i%2=0 then key seed else .unary .fst (.binary .pair (key seed) (.const .bottom)))
      (if i%2=0 then .var (expandedPartial 0) else .name (40+i%3))
      (.var (expandedResult ⟨i%2,by omega⟩))
  (List.range (1+seed%6)).foldl (fun t i => .mul t (leaf (i+1))) (leaf 0)
private def view : Ground → Ground × Multiset Ground × AddSummary Ground
  | .ternary .penc k r p => (k,r.composeLeaves,p.addSyntaxSummary)
  | t => (t,0,.empty)

def wrong_key_mutation (_ : Nat) : Bool :=
  let a : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed (.name 40) (.name 50) (.const .zero)
  let b : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed (.name 41) (.name 51) (.const .one)
  decide (normalizeRaw ((world false).eval ((a.mul b).recipeWith expandedOld)) =
    normalizeRaw ((world false).eval (compress (a.mul b))))
def singleton_strict_mutation (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed (key 0) (.name 40) (.const .zero)
  decide ((compress t).nodeCount < (t.recipeWith expandedOld).nodeCount)
def duplicate_nonce_mutation (_ : Nat) : Bool :=
  let p := (world false).eval (.var (expandedPartial 0))
  decide ((Term.binary .compose p p).composeLeaves = p.composeLeaves)

def check (seed : Nat) : Bool :=
  let t := tree seed
  let r := compress t
  decide (r.nodeCount < (t.recipeWith expandedOld).nodeCount) &&
    [false,true].all (fun swap =>
      decide (view (normalizeRaw ((world swap).eval (t.recipeWith expandedOld))) =
        view (normalizeRaw ((world swap).eval r))))

#eval campaign "incoherent constructed keys compress (negative control)" (∀ n : Nat, wrong_key_mutation n = true) 1 true
#eval campaign "singleton constructed compression is strict (negative control)" (∀ n : Nat, singleton_strict_mutation n = true) 1 true
#eval campaign "duplicate public partial nonce occurrence erased (negative control)" (∀ n : Nat, duplicate_nonce_mutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded constructed compression preserves published components and strict size" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded constructed compression backstop failed")
  IO.println "expanded constructed compression backstop: 2048 inputs, both swaps, two through seven constructors, published partial/result keys and components, delayed key aliases and repeated nonces"

end ExplainableCrypto.Helios.Symbolic.ExpandedConstructedExperiments
