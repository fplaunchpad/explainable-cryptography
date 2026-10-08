import ExplainableCrypto.Helios.Symbolic.ExpandedPairExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedPaddedExperiments
import ExplainableCrypto.Helios.Symbolic.PairTransportExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumExperiments
open ExplainableCrypto.Testing Historical General
private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10+i.val*(n+1)+j.val⟩
def check (seed : Nat) : Bool :=
  let n := seed%5
  let i : Fin 2 := ⟨seed%2,by omega⟩
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  [false,true].all fun swap =>
    let φ := expandedFrame (names n) swap left right []
    (List.range (fieldCount n)).all fun k =>
      let embed := fun r : Recipe 3 => r.subst (fun i => .var (expandedOld i))
      let a := embed (PairTransportExperiments.canonicalField n k i.succ)
      let b := embed (PairTransportExperiments.canonicalRemainder n k i.succ)
      let t : Recipe (ExpandedHandles n) := (Term.var (expandedOld i.succ)).drop k
      let p := Term.binary .pair a b
      normalizeRaw (φ.eval p) == normalizeRaw (φ.eval t) &&
        decide (t.nodeCount < p.nodeCount) && decide (k+1 ≤ a.nodeCount) &&
        !(normalizeRaw (φ.eval (.binary .pair b a)) == normalizeRaw (φ.eval t))

#eval campaign "expanded minimum children force minimum pair (negative control)" (∀ n : Nat, ExpandedPairExperiments.minimumChildren n = true) 1 true
#eval campaign "expanded partial has pair eta (negative control)" (∀ n : Nat, ExpandedPairExperiments.etaAll n = true) 1 true
#eval campaign "expanded empty voter tails stay distinct (negative control)" (∀ n : Nat, ExpandedPairExperiments.separateEmpty n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded canonical field and remainder reconstruct every honest tail" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded pair minimum backstop failed")
  IO.println "expanded pair minimum backstop: 2048 inputs, one through five candidates, every nonempty tail, both voters and swaps, one-candidate aggregate alias and empty remainder"

end ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumExperiments
