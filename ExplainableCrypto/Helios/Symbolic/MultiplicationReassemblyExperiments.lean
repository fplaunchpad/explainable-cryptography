import ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationReassemblyExperiments
open ExplainableCrypto.Testing
private def foldTerms : List (Recipe 3) → Recipe 3
  | [] => .const .bottom
  | a::xs => xs.foldl (Term.binary .mul) a
private def leaves : Ground → List Ground
  | .binary .mul a b => leaves a ++ leaves b
  | t => [t]
private def wrap (t : Recipe 3) : Recipe 3 := .unary .fst (.binary .pair t (.const .bottom))
private def view : Ground → Ground × Multiset Ground × AddSummary Ground
  | .ternary .penc k r m => (.ternary .penc k (.const .bottom) (.const .bottom),r.composeLeaves,m.addSyntaxSummary)
  | t => (t,0,.empty)
private def pairs (seed : Nat) : List (Recipe 3 × Recipe 3) :=
  (List.range (1+seed%7)).map fun j =>
    if (seed+j)%3=0 then
      let k : Recipe 3 := .name (60+j)
      (.binary .mul (.ternary .penc k (.name 40) (.const .zero)) (.ternary .penc k (.name 41) (.const .one)),
        .ternary .penc k (.binary .compose (.name 40) (.name 41)) (.const .one))
    else
      let t := if (seed+j)%2=0 then LocalRootSPOT.key else (.name (40+j%2) : Recipe 3)
      (wrap t,t)

def sourceOnly (_ : Nat) : Bool :=
  let φ : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .name 40⟩
  let ψ : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .name 41⟩
  let r : Recipe 1 := .var 0
  let m : Recipe 1 := .name 40
  decide (normalizeRaw (φ.eval r) = normalizeRaw (φ.eval m)) &&
    decide (normalizeRaw (ψ.eval r) = normalizeRaw (ψ.eval m))

def eraseDuplicate (_ : Nat) : Bool :=
  let t := LocalRootSPOT.key
  decide ((foldTerms [t,t]).nodeCount = (foldTerms [t]).nodeCount)

def check (seed : Nat) : Bool :=
  let ps := pairs seed
  let old := ps.map Prod.fst
  let new := ps.map Prod.snd
  let r := foldTerms old
  let m := foldTerms new.reverse
  (m.nodeCount+1 == (new.map fun t => t.nodeCount+1).sum) &&
  decide (m.nodeCount ≤ r.nodeCount) &&
  [false,true].all (fun swap =>
    let φ := LocalRootSPOT.world swap
    let es := old.map (fun t => view (normalizeRaw (φ.eval t)))
    let fs := new.reverse.map (fun t => view (normalizeRaw (φ.eval t)))
    decide (es.Perm fs) &&
      decide (((leaves (normalizeRaw (φ.eval r))).map view).Perm
        ((leaves (normalizeRaw (φ.eval m))).map view)))

#eval campaign "one-frame equality used as shared equality (negative control)" (∀ n : Nat, sourceOnly n = true) 1 true
#eval campaign "duplicate reassembly piece erased (negative control)" (∀ n : Nat, eraseDuplicate n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "shared-piece product reassembly preserves both values and exact new costs" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "multiplication reassembly backstop failed")
  IO.println "multiplication reassembly backstop: 2048 inputs, one to seven pieces, duplicate atoms, fusion groups and both swaps"

end ExplainableCrypto.Helios.Symbolic.MultiplicationReassemblyExperiments
