import ExplainableCrypto.Helios.Computational.BallotReplayStorage
import ExplainableCrypto.Helios.Computational.BallotKeyRecord
import ExplainableCrypto.Helios.Computational.BallotFiniteCacheControls
import Mathlib.Algebra.Field.ZMod

/-! Independent literal fixtures for storage offsets and complete key records.
The scalar type is a prime field; the group labels test records, not cryptography. -/
namespace ExplainableCrypto.Helios.Computational.BallotReplayStorageControls
open OracleComp OracleSpec BallotFiniteCacheControls

abbrev Scalar := ZMod 11
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def preloaded : BallotFiniteLoggedState Scalar Nat :=
  ((∅ : BallotFiniteCache Scalar Nat).insert key0 0, [])

def recorded (c : Scalar) : BallotFiniteLoggedState Scalar Nat :=
  ((∅ : BallotFiniteCache Scalar Nat).insert key0 c, [((),key0)])

/-- An actual empty execution retains the preloaded offset. Unqualified
cache/log equality is false even without any attacker or rejection behavior. -/
theorem preloaded_refutes_equal_counts :
    runBallotFiniteLogged (pure () : BallotOracleComp Scalar Nat Unit) preloaded =
      pure ((),preloaded) ∧ preloaded.1.entries.length = 1 ∧
      preloaded.2.length = 0 ∧ preloaded.1.entries.length ≠ preloaded.2.length := by
  refine ⟨?_,rfl,rfl,by decide⟩
  simp [runBallotFiniteLogged]

/-- One actual fresh-key request stores exactly its sampled answer and key. -/
theorem fresh_query_records_once :
    runBallotFiniteLogged
      (liftM ((BallotOracleSpec Scalar Nat).query (.inr key0))) (∅,[]) =
      (do let c ← FiatShamir.Fork.wrappedChallengeQuery Scalar; pure (c,recorded c)) := by
  simp [runBallotFiniteLogged,ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,recorded]

/-- The expected eight fields are fixed independently of the decoder. -/
theorem literal_key_layout : ballotKeyRecord key0 = [1,2,3,4,5,6,7,8] ∧
    ballotKeyOfRecord [1,2,3,4,5,6,7,8] = some key0 := ⟨rfl,rfl⟩

/-- Swapping two statement fields remains a different key; dropping a field
or retaining a trailing field is rejected by the record decoder. -/
theorem detects_key_layout_mutations :
    ballotKeyOfRecord [2,1,3,4,5,6,7,8] ≠ some key0 ∧
    ballotKeyOfRecord [2,3,4,5,6,7,8] = (none : Option (BallotForkPoint Nat)) ∧
    ballotKeyOfRecord [1,2,3,4,5,6,7,8,9] = (none : Option (BallotForkPoint Nat)) := by
  refine ⟨?_,rfl,rfl⟩
  intro h
  have he : (2 : Nat) = 1 := congrArg (fun key => key.1.generator) (Option.some.inj h)
  cases he

/-- Concrete post-miss state has one entry in each structure and both full
keys in the group projection; the sampled scalar answer remains present. -/
theorem recorded_cell_counts (c : Scalar) :
    (recorded c).1.entries.length = 1 ∧ (recorded c).2.length = 1 ∧
    ballotLoggedGroupRecord (recorded c) =
      [1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8] ∧
    ballotLoggedScalarRecord (recorded c) = [c] := ⟨rfl,rfl,rfl,rfl⟩

#print axioms preloaded_refutes_equal_counts
#print axioms fresh_query_records_once
#print axioms literal_key_layout
#print axioms detects_key_layout_mutations
#print axioms recorded_cell_counts
end ExplainableCrypto.Helios.Computational.BallotReplayStorageControls
