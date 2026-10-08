import ExplainableCrypto.Helios.Symbolic.ExpandedPublishedFrames
import ExplainableCrypto.Helios.Symbolic.OpaqueProtectionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedFrameExperiments
open ExplainableCrypto.Testing Historical General

def shiftedResult (_ : Nat) : Bool :=
  let φ := expandedFrame LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right []
  decide ((normalizeRaw (φ.value (expandedResult 0))).addSyntaxSummary = AddSummary.number 1)

def missingLastPartial (_ : Nat) : Bool :=
  let φ := expandedFrame LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right []
  normalizeRaw (Term.tuple [φ.value (expandedPartial 0)]) ==
    normalizeRaw ((finalFrame LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right []).value 3)

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    let rs := (List.range (seed%6)).map (fun i => ElectionTallyExperiments.publicBallot (40+i)
      (if (seed+i)%2=0 then .zero else .one))
    let ns := ProofObservationSPOT.oneNames
    let l := ProofObservationSPOT.oneLeft
    let r := ProofObservationSPOT.oneRight
    let φ := expandedFrame ns swap l r rs
    let ψ := finalFrame ns swap l r rs
    let e := expandedFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
    let f := finalFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
    (List.finRange 3).all (fun i => decide (φ.value (expandedOld i) = (frame ns swap l r).value i)) &&
    (List.finRange (ExpandedHandles 0)).all (fun i =>
      normalizeRaw (ψ.eval (expandedRecipes i)) == normalizeRaw (φ.value i)) &&
    (List.finRange 5).all (fun i => normalizeRaw (φ.eval (tupleRecipes i)) == normalizeRaw (ψ.value i)) &&
    (List.finRange (ExpandedHandles 1)).all (fun i =>
      normalizeRaw (f.eval (expandedRecipes i)) == normalizeRaw (e.value i)) &&
    (List.finRange 5).all (fun i => normalizeRaw (e.eval (tupleRecipes i)) == normalizeRaw (f.value i)) &&
    [0,1].all (fun j : Fin 2 =>
      decide ((normalizeRaw (e.value (expandedResult j))).addSyntaxSummary = AddSummary.number j.val) &&
      decide ((Term.var (expandedResult j) : Recipe (ExpandedHandles 1)).nodeCount = 1)))

#eval campaign "shifted last result slot (negative control)" (∀ n : Nat, shiftedResult n = true) 1 true
#eval campaign "last partial may be omitted on reconstruction (negative control)"
  (∀ n : Nat, missingLastPartial n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "both public frame presentations reconstruct every slot"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded frame backstop failed")
  IO.println "expanded frame backstop: 2048 inputs, one/two candidates, zero through five submissions, both swaps"

end ExplainableCrypto.Helios.Symbolic.ExpandedFrameExperiments
