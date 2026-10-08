import ExplainableCrypto.Helios.Symbolic.PairTransportSPOT

namespace ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextExperiments
open ExplainableCrypto.Testing
open Historical General

private def wrapped (k : Nat) (r : Recipe 3) : Recipe 3 :=
  (List.range k).foldl (fun t _ => .unary .fst (.binary .pair t (.const .bottom))) r

def omittedChildMinimum (_ : Nat) : Bool :=
  let a : Recipe 3 := .ternary .penc (.var 0) (wrapped 1 (.name 40)) (.const .zero)
  let b : Recipe 3 := .ternary .penc (.var 0) (.name 40) (.const .zero)
  !(normalizeRaw a == normalizeRaw b) || a.nodeCount ≤ b.nodeCount

def omittedKeyBudget (_ : Nat) : Bool :=
  let t : CiphertextAssembly 1 := .constructed (wrapped 1 (.var 0)) (.name 40) (.const .zero)
  t.recipe.nodeCount ≤ t.group.budget

def check (seed : Nat) : Bool :=
  let k := wrapped (seed % 4) (.var 0)
  let leaf (j : Nat) : CiphertextAssembly 1 :=
    .constructed (wrapped ((seed+j)%4) k) (.name (40+j)) (.const (if j%2=0 then .zero else .one))
  let pub := (List.range (seed % 5)).foldl (fun t j => .mul t (leaf (j+1))) (leaf 0)
  let honest : CiphertextAssembly 1 := .honest (⟨seed%2,by omega⟩,⟨seed%2,by omega⟩)
  let trees := [pub,honest,.mul pub honest,.mul honest pub,.mul (.mul pub honest) pub]
  (trees.all fun t => t.keyRecipe.nodeCount + t.group.budget ≤ t.recipe.nodeCount+1) &&
  (match pub.group with
  | .constructed r p =>
    let fused : Recipe 3 := .ternary .penc pub.keyRecipe r p
    decide (fused.nodeCount ≤ pub.recipe.nodeCount) &&
    [false,true].all (fun swap =>
      let φ := LocalRootSPOT.world swap
      normalizeRaw (φ.eval fused) == normalizeRaw (φ.eval pub.recipe))
  | _ => false)

#eval campaign "ciphertext closure without minimum children (negative control)"
  (∀ n : Nat, omittedChildMinimum n = true) 1 true
#eval campaign "group budget counts the selected key (negative control)"
  (∀ n : Nat, omittedKeyBudget n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "ciphertext regrouping includes key and all public components" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "constructed ciphertext backstop failed")
  IO.println "constructed ciphertext backstop: 2048 inputs, five assembly forms, both swaps"

end ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextExperiments
