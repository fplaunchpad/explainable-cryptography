import ExplainableCrypto.Helios.Symbolic.ExpandedObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumExperiments
open ExplainableCrypto.Testing Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
private def foldTerms : List (Recipe (ExpandedHandles 1)) → Recipe (ExpandedHandles 1)
  | [] => .const .bottom
  | a::xs => xs.foldl (Term.binary .mul) a
private def wrap (t : Recipe (ExpandedHandles 1)) := Term.unary .fst (.binary .pair t (.const .bottom))
private def view (t : Ground) : Nat × Ground × Multiset Ground × AddSummary Ground :=
  match t with
  | .ternary .penc k r m => (11,k,r.composeLeaves,m.addSyntaxSummary)
  | .binary .add _ _ | .const .zero | .const .one => (9,.const .bottom,0,t.addSyntaxSummary)
  | t => (0,t,0,.empty)
private def pairs (seed : Nat) : List (Recipe (ExpandedHandles 1) × Recipe (ExpandedHandles 1)) :=
  let marker : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  (marker,marker) :: (List.range (1+seed%7)).map fun j =>
    if (seed+j)%3=0 then
      let k : Recipe (ExpandedHandles 1) := .binary .pair marker (.name (60+j))
      (.binary .mul (.ternary .penc k (.name 40) (.const .zero)) (.ternary .penc k (.name 41) (.const .one)),
       .ternary .penc k (.binary .compose (.name 40) (.name 41)) (.const .one))
    else
      let t : Recipe (ExpandedHandles 1) := if (seed+j)%2=0 then marker else .var (expandedResult 1)
      (wrap t,t)

def one_frame_mutation (_ : Nat) : Bool :=
  let φ : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .name 40⟩
  let ψ : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .name 41⟩
  decide (normalizeRaw (φ.eval (.var 0)) = normalizeRaw (φ.eval (.name 40))) &&
    decide (normalizeRaw (ψ.eval (.var 0)) = normalizeRaw (ψ.eval (.name 40)))
def duplicate_cost_mutation (_ : Nat) : Bool :=
  let p : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  decide ((foldTerms [p,p]).nodeCount = (foldTerms [p]).nodeCount)
def unfused_target_mutation (_ : Nat) : Bool :=
  let c : Ground := .ternary .penc (.name 40) (.name 50) (.const .zero)
  decide ((Term.binary .mul c c).mulLeaves.card = (normalizeRaw (.binary .mul c c)).mulLeaves.card)

def check (seed : Nat) : Bool :=
  let ps := pairs seed
  let old := ps.map Prod.fst
  let new := ps.map Prod.snd
  let r := foldTerms old
  let m := foldTerms new.reverse
  decide (m.nodeCount+1 = (new.map fun t => t.nodeCount+1).sum) &&
  decide (m.nodeCount ≤ r.nodeCount) &&
  [false,true].all (fun swap =>
    let φ := world swap
    decide (((normalizeRaw (φ.eval r)).mulLeaves.map view) =
      ((normalizeRaw (φ.eval m)).mulLeaves.map view)) &&
    decide ((normalizeRaw (φ.eval r)).mulLeaves.card ≥ 2))

#eval campaign "source-only replacement used for shared minimum (negative control)" (∀ n : Nat, one_frame_mutation n = true) 1 true
#eval campaign "duplicate expanded piece cost erased (negative control)" (∀ n : Nat, duplicate_cost_mutation n = true) 1 true
#eval campaign "unfused target used as normal partition (negative control)" (∀ n : Nat, unfused_target_mutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded shared product reassembly preserves both values and exact piece costs" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded multiplication minimum backstop failed")
  IO.println "expanded multiplication minimum backstop: 2048 inputs, both swaps, two through eight pieces, actual partial/result handles, duplicates, delayed recipes and fused constructed groups"

end ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumExperiments
