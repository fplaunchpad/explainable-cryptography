import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedHonestExperiments
open ExplainableCrypto.Testing Historical General
abbrev world := ExpandedConstructedExperiments.world
private def index (seed i : Nat) : HonestIndex 1 :=
  (⟨(seed+i)%2,by omega⟩,⟨(seed/2+i/2)%2,by omega⟩)
private def tree (seed : Nat) : Combination (HonestIndex 1) :=
  (List.range (seed%8)).foldl (fun t i => .mul (.leaf (index seed (i+1))) t) (.leaf (index seed 0))
private def embedded (t : Combination (HonestIndex 1)) : Recipe (ExpandedHandles 1) :=
  (combinationRecipe t).subst (fun i => .var (expandedOld i))
private def expectedCost (seed : Nat) : Nat :=
  ((List.range (1+seed%8)).map (fun i => (index seed i).2.val+3)).sum
private def expectedNonces (seed : Nat) : Multiset Ground :=
  ((List.range (1+seed%8)).map (fun i => .name (LocalRootSPOT.names.nonce (index seed i).1 (index seed i).2)) : List Ground)
private def nonceView : Ground → Multiset Ground
  | .ternary .penc _ r _ => r.composeLeaves
  | _ => 0

def uniform_selector_cost_mutation (_ : Nat) : Bool :=
  decide ((embedded (.leaf (0,1))).nodeCount = 2)
def erase_duplicate_mutation (_ : Nat) : Bool :=
  decide (nonceView (normalizeRaw ((world false).eval (embedded (.mul (.leaf (0,0)) (.leaf (0,0)))))) =
    nonceView (normalizeRaw ((world false).eval (embedded (.leaf (0,0))))))
def published_selector_mutation (_ : Nat) : Bool :=
  decide (nonceView (normalizeRaw ((world false).eval (.unary .fst (.var (expandedPartial 0))))) =
    nonceView (normalizeRaw ((world false).eval (embedded (.leaf (0,0))))))
def check (seed : Nat) : Bool :=
  decide ((embedded (tree seed)).nodeCount+1 = expectedCost seed) &&
    [false,true].all (fun swap =>
      decide (nonceView (normalizeRaw ((world swap).eval (embedded (tree seed)))) = expectedNonces seed))

#eval campaign "all honest selector indices cost two (negative control)" (∀ n : Nat, uniform_selector_cost_mutation n = true) 1 true
#eval campaign "honest duplicate nonce occurrence erased (negative control)" (∀ n : Nat, erase_duplicate_mutation n = true) 1 true
#eval campaign "published partial projection is honest ciphertext (negative control)" (∀ n : Nat, published_selector_mutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded honest combinations retain indexed costs and nonce occurrences" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded honest combination backstop failed")
  IO.println "expanded honest combination backstop: 2048 inputs, both swaps, one through eight selectors, both voters and indices, repeated nonce occurrences"

end ExplainableCrypto.Helios.Symbolic.ExpandedHonestExperiments
