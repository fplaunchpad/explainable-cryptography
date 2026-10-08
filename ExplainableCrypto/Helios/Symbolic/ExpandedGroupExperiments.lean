import ExplainableCrypto.Helios.Symbolic.ExpandedMulExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedGroupExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private def nonce (swap : Bool) (count : Nat) : Ground :=
  (List.range count).foldl (fun t _ => .binary .compose t (.name (names.nonce 0 0)))
    ((world swap).eval (.var (expandedPartial 0)))

def duplicateMutation (_ : Nat) : Bool :=
  decide ((normalizeRaw (nonce false 1)).composeLeaves = (normalizeRaw (nonce false 2)).composeLeaves)

def paddingMutation (_ : Nat) : Bool :=
  let r := (world false).eval (.binary .add (.name 40) (.var (expandedResult 0)))
  decide ((normalizeRaw r).addSyntaxSummary = (Term.name 40 : Ground).addSyntaxSummary)

def opaqueMutation (_ : Nat) : Bool :=
  ((world false).eval (.var (expandedPartial 0))).nonceSafe names.restricted

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let count := 1+seed%5
    let k := (seed/5)%2
    let r := nonce swap count
    let trustee :=  (world swap).eval (.var (expandedPartial 0))
    let result := (world swap).eval (.var (expandedResult ⟨k,by omega⟩))
    let delayed := Term.unary .fst (.binary .pair r (.name 50))
    decide ((normalizeRaw r).composeLeaves.card = count+1) &&
    decide ((normalizeRaw delayed).composeLeaves = (normalizeRaw r).composeLeaves) &&
    (normalizeRaw trustee).opaqueSafe names.restricted &&
    let p := Term.binary .add (.name 40) result
    decide ((normalizeRaw p).addSyntaxSummary.numeric = some k) &&
    decide ((normalizeRaw (.binary .add p (.const .zero))).addSyntaxSummary = (normalizeRaw p).addSyntaxSummary))

#eval campaign "honest nonce occurrences collapse (negative control)" (∀ n : Nat, duplicateMutation n = true) 1 true
#eval campaign "public payload zero padding erased (negative control)" (∀ n : Nat, paddingMutation n = true) 1 true
#eval campaign "published partial satisfies old strong nonce safety (negative control)" (∀ n : Nat, opaqueMutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "opaque public nonce remainders retain honest occurrences and numeric padding" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded group backstop failed")
  IO.println "expanded group backstop: 2048 inputs, both swaps, one through five repeated honest nonces, public partials, both result slots and delayed projections"

end ExplainableCrypto.Helios.Symbolic.ExpandedGroupExperiments
