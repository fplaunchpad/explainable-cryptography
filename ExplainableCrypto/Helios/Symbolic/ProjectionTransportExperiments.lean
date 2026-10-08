import ExplainableCrypto.Helios.Symbolic.LocalRootSPOT

namespace ExplainableCrypto.Helios.Symbolic.ProjectionTransportExperiments
open ExplainableCrypto.Testing
open Historical General

private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10 + i.val * (n+1) + j.val⟩
private def world (n : Nat) (swap : Bool) :=
  frame (names n) swap (BitCandidate.selected (0 : Fin (n+1))).substitution (BitCandidate.abstain n).substitution

def aggregateAlwaysMinimum (_ : Nat) : Bool :=
  let a : Recipe 3 := (Term.var 1).project 2
  let c : Recipe 3 := (Term.var 1).project 1
  !(normalizeRaw ((world 0 false).eval a) == normalizeRaw ((world 0 false).eval c)) ||
    a.nodeCount ≤ c.nodeCount

def check (seed : Nat) : Bool :=
  let n := seed % 5
  let aggregate : Recipe 3 := (Term.var 1).project (2 * (n+1))
  let canonical : Recipe 3 := if n = 0 then (Term.var 1).project 1 else aggregate
  let a : Recipe 3 := .name (40 + seed % 3)
  let b : Recipe 3 := .var 2
  let fstPair := Term.unary .fst (.binary .pair a b)
  let sndPair := Term.unary .snd (.binary .pair a b)
  [false,true].all fun swap =>
    let φ := world n swap
    (normalizeRaw (φ.eval aggregate) == normalizeRaw (φ.eval canonical)) &&
    (canonical.nodeCount ≤ aggregate.nodeCount) &&
    (normalizeRaw (φ.eval fstPair) == normalizeRaw (φ.eval a)) &&
    (normalizeRaw (φ.eval sndPair) == normalizeRaw (φ.eval b)) &&
    (normalizeRaw (φ.eval ((Term.var 1).drop (fieldCount n))) == .const .bottom) &&
    ((List.range (n+2)).all fun j =>
      let k := n+1+j
      let field : Recipe 3 := (Term.var 1).project k
      let minimumField : Recipe 3 := if n = 0 && k = 2 then (Term.var 1).project 1 else field
      (normalizeRaw (φ.eval field) == normalizeRaw (φ.eval minimumField)) &&
      (((Term.var 1 : Recipe 3).drop k).nodeCount ≤ minimumField.nodeCount + 2))

#eval campaign "every honest aggregate selector is minimum (negative control)"
  (∀ n : Nat, aggregateAlwaysMinimum n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "canonical proof selectors, explicit pairs and empty tails" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "projection transport backstop failed")
  IO.println "projection transport backstop: 2048 inputs, one through five candidates, both swaps"

end ExplainableCrypto.Helios.Symbolic.ProjectionTransportExperiments
