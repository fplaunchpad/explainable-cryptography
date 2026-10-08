import ExplainableCrypto.Helios.Symbolic.AdditionMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumExperiments
open ExplainableCrypto.Testing

private def foldTerms : List (Recipe 3) → Recipe 3
  | [] => .const .bottom
  | a::xs => xs.foldl (Term.binary .mul) a

private def wrap (t : Recipe 3) : Nat → Recipe 3
  | 0 => t
  | n+1 => .unary .fst (.binary .pair (wrap t n) (.const .bottom))

def omittedDuplicate (_ : Nat) : Bool :=
  let t : Recipe 3 := .binary .mul LocalRootSPOT.key LocalRootSPOT.key
  t.nodeCount+1 == LocalRootSPOT.key.nodeCount+1

def check (seed : Nat) : Bool :=
  let xs := (List.range (1+seed%7)).map fun j =>
    if (seed+j)%2=0 then LocalRootSPOT.key else (.name (40+j%2) : Recipe 3)
  let ys := xs.reverse.mapIdx fun j t => wrap t ((seed+j)%3)
  let source := foldTerms xs
  let competitor := foldTerms ys
  (source.nodeCount+1 == (xs.map fun t => t.nodeCount+1).sum) &&
  (competitor.nodeCount+1 == (ys.map fun t => t.nodeCount+1).sum) &&
  decide (source.nodeCount ≤ competitor.nodeCount) &&
  [false,true].all (fun swap =>
    let φ := LocalRootSPOT.world swap
    decide ((xs.map (fun t => normalizeRaw (φ.eval t))).Perm
      (ys.map (fun t => normalizeRaw (φ.eval t))))) &&
  MultiplicationObservationExperiments.partitionCheck seed

#eval campaign "duplicate piece cost omitted (negative control)" (∀ n : Nat, omittedDuplicate n = true) 1 true
#eval campaign "unfused endpoint used for factor matching (negative control)"
  (∀ n : Nat, MultiplicationObservationExperiments.unfusedBag n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "normal partition matching and exact piece-cost bounds" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "multiplication minimum partition backstop failed")
  IO.println "multiplication minimum partition backstop: 2048 inputs, repeated non-atomic pieces, wrappers, fusion budgets and both swaps"

end ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumExperiments
