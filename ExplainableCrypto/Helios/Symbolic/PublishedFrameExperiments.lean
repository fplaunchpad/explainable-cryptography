import ExplainableCrypto.Helios.Symbolic.PublishedFrames
import ExplainableCrypto.Helios.Symbolic.SharedTallySPOT

namespace ExplainableCrypto.Helios.Symbolic.PublishedFrameExperiments
open ExplainableCrypto.Testing Historical General

def individualFrame (swap : Bool) : Frame ProofObservationSPOT.oneNames.restricted 4 :=
  let φ := ProofObservationSPOT.oneWorld swap
  φ.extend (candidateTuple (n := 0) (fun j => .binary .partialDecrypt
    (.name ProofObservationSPOT.oneNames.secretKey) (φ.eval ((Term.var 1).project j.val))))
def individualProbe : Recipe 4 :=
  .binary .dec ((Term.var 3).project 0) (Recipe.lift ((Term.var 1 : Recipe 3).project 0))

def unsafeIndividualPublication (_ : Nat) : Bool :=
  normalizeRaw ((individualFrame false).eval individualProbe) ==
    normalizeRaw ((individualFrame true).eval individualProbe)

def omitLastCandidate (_ : Nat) : Bool :=
  let missing := Term.tuple [tallyPartial LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right [] 0]
  let b := tallyCiphertext LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right [] 1
  decide ((normalizeRaw (.binary .dec (missing.project 1) b)).addSyntaxSummary = AddSummary.number 1)

def check (seed : Nat) : Bool :=
  let indices := List.range (seed%6)
  let rs := indices.map (fun i => ElectionTallyExperiments.publicBallot (40+i)
    (if (seed+i)%2=0 then .zero else .one))
  let expected := 1 + (indices.map (fun i => (seed+i)%2)).sum
  [false,true].all (fun swap =>
    let ns := ProofObservationSPOT.oneNames
    let left := ProofObservationSPOT.oneLeft
    let right := ProofObservationSPOT.oneRight
    let p := partialFrame ns swap left right rs
    let f := finalFrame ns swap left right rs
    let source := frame ns swap left right
    decide (f.value 0=source.value 0 ∧ f.value 1=source.value 1 ∧ f.value 2=source.value 2) &&
    (normalizeRaw (p.eval (resultRecipe (n := 0) rs)) == normalizeRaw (f.value 4)) &&
    decide ((normalizeRaw (f.eval ((Term.var 4).project 0))).addSyntaxSummary = AddSummary.number expected) &&
    [0,1].all (fun j : Fin 2 =>
      let f2 := finalFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
      decide ((normalizeRaw (f2.eval ((Term.var 4).project j.val))).addSyntaxSummary = AddSummary.number j.val)))

#eval campaign "equal tally permits individual partial publication (negative control)"
  (∀ n : Nat, unsafeIndividualPublication n = true) 1 true
#eval campaign "partial tuple may omit its last candidate (negative control)"
  (∀ n : Nat, omitLastCandidate n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "published frames retain handles, complete tuples and actual E6 results"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "published frame backstop failed")
  IO.println "published frame backstop: 2048 inputs, one/two candidates, zero through five submissions and both swaps"

end ExplainableCrypto.Helios.Symbolic.PublishedFrameExperiments
