import ExplainableCrypto.Helios.Computational.BallotFiniteProgrammed
import Mathlib.Algebra.Field.ZMod

/-! Independent literal transition controls over ZMod 11. These cover cache
collisions, retained proof challenges, sticky failure and duplicate history. -/
namespace ExplainableCrypto.Helios.Computational.BallotFiniteProgrammedControls
open OracleComp OracleSpec
abbrev Scalar := ZMod 11
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def stmt0 : BallotStatement Scalar := ⟨1,2,(3,4)⟩
def stmt1 : BallotStatement Scalar := ⟨1,2,(5,6)⟩
def transcript (challenge : Scalar) : BallotCommitment Scalar × Scalar × BallotResponse Scalar :=
  (((0,0),(0,0)),challenge,(0,0,0))
def first : BallotFiniteProgrammedState Scalar Scalar :=
  (BallotFiniteProgrammedState.empty.program stmt0 (transcript 0)).2
def collision : BallotFiniteProgrammedState Scalar Scalar :=
  (first.program stmt0 (transcript 1)).2

/-- A fresh key is inserted, recorded and unflagged. -/
theorem fresh_records : first.cache.lookup (stmt0,(transcript 0).1) = some 0 ∧
    first.bad = false ∧ first.programmed = [stmt0] := by decide

/-- Conflicting programming preserves the old answer and returns the new proof;
its flag prevents treating this execution as successful programming. -/
theorem conflict_retains_old_answer :
    collision.cache.lookup (stmt0,(transcript 1).1) = some 0 ∧
    collision.bad = true ∧ collision.programmed = [stmt0,stmt0] ∧
    (first.program stmt0 (transcript 1)).1.zero.challenge +
      (first.program stmt0 (transcript 1)).1.one.challenge = 1 := by decide

/-- Even agreeing occupied answers count as collisions. -/
theorem agreeing_hit_flagged : (first.program stmt0 (transcript 0)).2.bad = true := by decide

/-- A later fresh request neither clears failure nor deduplicates the history. -/
theorem fresh_after_bad_sticky :
    (collision.program stmt1 (transcript 1)).2.bad = true ∧
    (collision.program stmt1 (transcript 1)).2.programmed = [stmt1,stmt0,stmt0] ∧
    (collision.program stmt1 (transcript 1)).2.cache.lookup (stmt0,(transcript 0).1) = some 0 ∧
    (collision.program stmt1 (transcript 1)).2.cache.lookup (stmt1,(transcript 1).1) = some 1 := by
  decide

/-- A raw hit after a flagged request returns the cached answer without drawing,
clearing the flag or recording another proof request. -/
theorem raw_hit_preserves_runtime :
    ((ballotFiniteProgrammedRaw (F := Scalar) (G := Scalar))
      (.inr (stmt0,(transcript 1).1))).run collision = pure ((0 : Scalar),collision) := by
  have h : collision.cache.lookup (stmt0,(transcript 1).1) = some 0 := by decide
  simp [ballotFiniteProgrammedRaw,QueryImpl.add,StateT.run,h]

/-- A programming collision adds history while retaining one cache entry.
This refutes cache/history equality and history deduplication in the same state. -/
theorem storage_collision_offset : first.cache.entries.length = 1 ∧
    first.programmed.length = 1 ∧ collision.cache.entries.length = 1 ∧
    collision.programmed.length = 2 ∧
    collision.cache.entries.length ≠ collision.programmed.length := by decide

/-- A fresh request after a collision adds one entry to each structure while
retaining the existing offset and duplicate history. -/
theorem fresh_storage_growth :
    (collision.program stmt1 (transcript 1)).2.cache.entries.length = 2 ∧
    (collision.program stmt1 (transcript 1)).2.programmed.length = 3 := by decide

#print axioms fresh_records
#print axioms conflict_retains_old_answer
#print axioms agreeing_hit_flagged
#print axioms fresh_after_bad_sticky
#print axioms raw_hit_preserves_runtime
#print axioms storage_collision_offset
#print axioms fresh_storage_growth
end ExplainableCrypto.Helios.Computational.BallotFiniteProgrammedControls
