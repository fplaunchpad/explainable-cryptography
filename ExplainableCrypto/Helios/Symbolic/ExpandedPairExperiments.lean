import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPairExperiments
open ExplainableCrypto.Testing Historical General
abbrev world (swap : Bool) := expandedFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []

def etaAll (_ : Nat) : Bool :=
  let r : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  normalizeRaw ((world false).eval r) == normalizeRaw ((world false).eval (.binary .pair (.unary .fst r) (.unary .snd r)))

def separateEmpty (_ : Nat) : Bool :=
  normalizeRaw ((world false).eval ((Term.var (expandedOld 1)).drop 5)) !=
    normalizeRaw ((world false).eval ((Term.var (expandedOld 2)).drop 5))

abbrev pairHandle : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .binary .pair (.name 40) (.name 41)⟩
def minimumChildren (_ : Nat) : Bool :=
  let r : Recipe 1 := .binary .pair (.name 40) (.name 41)
  decide (r.nodeCount ≤ (Term.var (0 : Fin 1)).nodeCount) &&
    normalizeRaw (pairHandle.eval r) == normalizeRaw (pairHandle.eval (.var 0))

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let φ := world swap
    let i : Fin 2 := ⟨seed%2,by omega⟩
    let k := seed%5
    let tail : Recipe (ExpandedHandles 1) := (Term.var (expandedOld i.succ)).drop k
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial i)
    let b : Recipe (ExpandedHandles 1) := .var (expandedResult i)
    let pair := Term.binary .pair a (.binary .partialDecrypt a b)
    normalizeRaw (φ.eval tail) == normalizeRaw (φ.eval (.binary .pair (.unary .fst tail) (.unary .snd tail))) &&
    normalizeRaw (φ.eval (.unary .fst pair)) == normalizeRaw (φ.eval a) &&
    normalizeRaw (φ.eval (.unary .snd pair)) == normalizeRaw (φ.eval (.binary .partialDecrypt a b)) &&
    (List.range 5).all (fun l =>
      decide ((normalizeRaw (φ.eval tail) == normalizeRaw (φ.eval ((Term.var (expandedOld i.succ)).drop l))) = decide (k=l))))

#eval campaign "pair eta on published partial (negative control)" (∀ n : Nat, etaAll n = true) 1 true
#eval campaign "different voters have distinct empty tails (negative control)" (∀ n : Nat, separateEmpty n = true) 1 true
#eval campaign "minimum children prevent borrowed pair compression (negative control)" (∀ n : Nat, minimumChildren n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded pairs retain ordered fields and nonempty tail lengths" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded pair backstop failed")
  IO.println "expanded pair backstop: 2048 inputs, both voters and swaps, all five nonempty tail positions"

end ExplainableCrypto.Helios.Symbolic.ExpandedPairExperiments
