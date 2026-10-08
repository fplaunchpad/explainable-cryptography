import ExplainableCrypto.Helios.Symbolic.HonestProductMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.ConstructedCompressionExperiments
open ExplainableCrypto.Testing Historical General

private def compress (t : CiphertextAssembly 1) : Recipe 3 :=
  match t.group with
  | .constructed r p => .ternary .penc t.keyRecipe r p
  | _ => .const .bottom

def wrongKey (_ : Nat) : Bool :=
  let a : Ground := .ternary .penc (.name 40) (.name 41) (.const .zero)
  let b : Ground := .ternary .penc (.name 42) (.name 43) (.const .one)
  normalizeRaw (.binary .mul a b) ==
    normalizeRaw (.ternary .penc (.name 40) (.binary .compose (.name 41) (.name 43))
      (.binary .add (.const .zero) (.const .one)))

def singletonStrict (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 := .constructed (.var 0) (.name 40) (.const .zero)
  decide ((compress t).nodeCount < t.recipe.nodeCount)

def check (seed : Nat) : Bool :=
  let k : Recipe 3 := if seed%2=0 then .var 0 else LocalRootSPOT.key
  let leaf (i : Nat) : CiphertextAssembly 1 :=
    .constructed (if i%2=0 then k else .unary .fst (.binary .pair k (.const .bottom)))
      (.name (40+i%3)) (if i%2=0 then .const .zero else .const .one)
  let t := (List.range (1+seed%6)).foldl (fun t i => .mul t (leaf (i+1))) (leaf 0)
  let r := compress t
  decide (r.nodeCount < t.recipe.nodeCount) &&
    [false,true].all (fun swap =>
      let φ := LocalRootSPOT.world swap
      normalizeRaw (φ.eval t.recipe) == normalizeRaw (φ.eval r))

#eval campaign "wrong-key ciphertext fusion (negative control)" (∀ n : Nat, wrongKey n = true) 1 true
#eval campaign "strict compression of a singleton (negative control)" (∀ n : Nat, singletonStrict n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "constructed-only compression preserves values and strictly lowers cost" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "constructed compression backstop failed")
  IO.println "constructed compression backstop: 2048 inputs, two to seven constructors, non-atomic/reducible keys and both swaps"

end ExplainableCrypto.Helios.Symbolic.ConstructedCompressionExperiments
