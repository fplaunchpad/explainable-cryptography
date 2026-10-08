import ExplainableCrypto.Helios.Symbolic.MixedCompressionSPOT

namespace ExplainableCrypto.Helios.Symbolic.PaddedMinimumExperiments
open ExplainableCrypto.Testing
private def fold : List (Recipe 3) → Recipe 3
  | [] => .const .zero
  | x::xs => xs.foldl (Term.binary .add) x
private def pad (r : Recipe 3) : Recipe 3 := .binary .add r (.const .zero)

def eraseOne (_ : Nat) : Bool :=
  decide ((pad (.binary .add (.const .one) (.const .one))).addSyntaxSummary =
    (pad (.const .one)).addSyntaxSummary)
def eraseAtom (_ : Nat) : Bool :=
  decide ((pad (.binary .add LocalRootSPOT.key LocalRootSPOT.key)).addSyntaxSummary =
    (pad LocalRootSPOT.key).addSyntaxSummary)
def unpaddedCancellation (_ : Nat) : Bool :=
  decide ((pad LocalRootSPOT.key).addSyntaxSummary = LocalRootSPOT.key.addSyntaxSummary)

def check (seed : Nat) : Bool :=
  let xs := (List.range (1+seed%7)).map fun i =>
    match (seed/7+i)%4 with
    | 0 => (Term.const .zero : Recipe 3)
    | 1 => .const .one
    | 2 => .name 40
    | _ => LocalRootSPOT.key
  let r := fold xs
  let kept := xs.filter (fun r => r != .const .zero)
  let s := fold kept
  let atomCost := (xs.map fun r => if r == .const .zero || r == .const .one then 0 else r.nodeCount+1).sum
  let ones := (xs.filter (fun r => r == .const .one)).length
  decide (s.nodeCount+1 = max 2 (atomCost+2*ones)) && decide (s.nodeCount≤r.nodeCount) &&
    decide ((pad r).addSyntaxSummary = (pad s).addSyntaxSummary) &&
    [false,true].all (fun swap =>
      let φ := LocalRootSPOT.world swap
      decide ((normalizeRaw (φ.eval (pad r))).addSyntaxSummary =
        (normalizeRaw (φ.eval (pad s))).addSyntaxSummary))

#eval campaign "padded payload loses a one (negative control)" (∀ n : Nat, eraseOne n = true) 1 true
#eval campaign "padded payload loses a non-atomic occurrence (negative control)" (∀ n : Nat, eraseAtom n = true) 1 true
#eval campaign "padding equality mistaken for raw equality (negative control)" (∀ n : Nat, unpaddedCancellation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "zero-padded payload representatives attain exact occurrence costs" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "padded minimum backstop failed")
  IO.println "padded minimum backstop: 2048 inputs, one through seven leaves, non-atomic duplicates and both swaps"

end ExplainableCrypto.Helios.Symbolic.PaddedMinimumExperiments
