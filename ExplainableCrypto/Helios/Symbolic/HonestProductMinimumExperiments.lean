import ExplainableCrypto.Helios.Symbolic.MultiplicationReassemblySPOT

namespace ExplainableCrypto.Helios.Symbolic.HonestProductMinimumExperiments
open ExplainableCrypto.Testing Historical General

private def foldCombination {α : Type} (a : α) (xs : List α) : Combination α :=
  xs.foldl (fun t i => .mul t (.leaf i)) (.leaf a)
private def assembly {n : Nat} : Combination (HonestIndex n) → CiphertextAssembly n
  | .leaf i => .honest i
  | .mul a b => .mul (assembly a) (assembly b)
private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10+i.val*(n+1)+j.val⟩

def check (seed : Nat) : Bool :=
  let n := seed%5
  let index (j : Nat) : HonestIndex n :=
    (⟨(seed+j)%2,by omega⟩,⟨(seed+j/2)%(n+1),Nat.mod_lt _ (by omega)⟩)
  let xs := (List.range (seed%7)).map index
  let t := foldCombination (index 0) xs
  let u := foldCombination (index 0) xs.reverse
  decide ((assembly t).group = .honest t) &&
  decide ((assembly t).recipe = combinationRecipe t) &&
  (combinationRecipe t).nodeCount+1 == ((t.indices.map fun i => i.2.val+3).sum) &&
  decide (t.indices = u.indices) && (combinationRecipe t).nodeCount == (combinationRecipe u).nodeCount &&
  [false,true].all (fun swap =>
    let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
    let right := (BitCandidate.abstain n).substitution
    let φ := frame (names n) swap left right
    (index 0 :: xs).all (fun i =>
      normalizeRaw (φ.eval ((Term.var i.1.succ).project i.2.val)) ==
        normalizeRaw (ciphertext (names n) i.1 (choice swap left right i.1).value i.2)))

#eval campaign "honest product minimum without nonce freshness (negative control)"
  (∀ n : Nat, CiphertextSelectorExperiments.collidingMinimum n = true) 1 true
#eval campaign "honest product occurrences erased (negative control)"
  (∀ n : Nat, CiphertextSelectorExperiments.lostMultiplicity n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "honest product occurrence costs and assembly reconstruction" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "honest product minimum backstop failed")
  IO.println "honest product minimum backstop: 2048 inputs, one to five candidates, one to seven occurrences and both swaps"

end ExplainableCrypto.Helios.Symbolic.HonestProductMinimumExperiments
