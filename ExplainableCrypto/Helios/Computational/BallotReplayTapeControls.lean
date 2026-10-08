import ExplainableCrypto.Helios.Computational.BallotReplayTape

/-! Literal branching and malformed-tape controls. Tags represent distinct
operations; answers affect which operation follows. -/
namespace ExplainableCrypto.Helios.Computational.BallotReplayTapeControls
open PFunctor.FreeM
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

abbrev commands : PFunctor.{0,0} := ⟨Bool,fun _ => Fin 2⟩
def branching : PFunctor.FreeM commands Nat := .liftBind false fun a =>
  if a = 0 then .pure 7 else .liftBind true fun b => .pure b.val
def saved : PFunctor.TraceList commands := [⟨false,1⟩,⟨true,0⟩]

/-- The supplied answer determines the later branch and final result. -/
theorem reconstructs_branch :
    (ballotReplayReadTape branching saved).map (output branching) = some 0 ∧
    (ballotReplayReadTape branching [⟨false,0⟩]).map (output branching) = some 7 := by decide

/-- Same answer values under the wrong operation tags cannot be replayed. -/
theorem rejects_wrong_tag :
    (ballotReplayReadTape branching [⟨false,1⟩,⟨false,0⟩]).isNone = true := by decide

/-- Neither a missing suffix nor an ignored trailing event is a complete path. -/
theorem rejects_truncation_and_trailing :
    (ballotReplayReadTape branching [⟨false,1⟩]).isNone = true ∧
    (ballotReplayReadTape branching [⟨false,0⟩,⟨true,0⟩]).isNone = true := by decide

/-- Reordering events or dropping the initial uniform-labelled event fails. -/
theorem rejects_reorder_and_drop :
    (ballotReplayReadTape branching [⟨true,0⟩,⟨false,1⟩]).isNone = true ∧
    (ballotReplayReadTape branching [⟨true,0⟩]).isNone = true := by decide

def repeated : PFunctor.FreeM commands Nat := .liftBind true fun _ =>
  .liftBind false fun _ => .liftBind true fun b => .pure b.val
def repeatedTape : PFunctor.TraceList commands := [⟨true,0⟩,⟨false,1⟩,⟨true,1⟩]

/-- Decoding and locating the second identical hash tag retains the two-event
prefix, including the intervening different operation. -/
theorem physical_second_occurrence :
    (do let path ← ballotReplayReadTape repeated repeatedTape
        let located ← PFunctor.FreeM.Cursor.locateAt? true repeated path 1
        pure located.occurrence.before.length) = some 2 := by decide

#print axioms reconstructs_branch
#print axioms rejects_wrong_tag
#print axioms rejects_truncation_and_trailing
#print axioms rejects_reorder_and_drop
#print axioms physical_second_occurrence
end ExplainableCrypto.Helios.Computational.BallotReplayTapeControls
