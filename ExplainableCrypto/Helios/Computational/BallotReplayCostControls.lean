import ExplainableCrypto.Helios.Computational.BallotReplayCost
import ExplainableCrypto.Helios.Computational.BallotJointReplayControls

/-! Cost controls count the original run and uniform queries, and expose that
local functions have zero cost in the query metric. -/
namespace ExplainableCrypto.Helios.Computational.BallotReplayCostControls
open OracleComp OracleSpec BallotForkControls StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

/-- Apply the general fourfold bound to the actual tagged honest extractor. -/
theorem tagged_joint_four_queries : BallotJointReplayControls.taggedJoint.IsTotalQueryBound 4 := by
  apply ballotJointReplay_total_query_bound taggedProgram (fun _ => Prod.snd) 1 1
  unfold taggedProgram
  rw [isTotalQueryBound_iff_isRollBound,PFunctor.FreeM.isRollBound_map_iff]
  unfold honestProgram strongBallotProofWithCoinsOracle ballotChallengeOracle
  simp only [bind_assoc,pure_bind]
  exact ⟨by decide,fun _ => trivial⟩

def oneCoin : ProbComp (Fin 2) := liftM (unifSpec.query 1)
def fourCoins : ProbComp Unit := do
  let _ ← oneCoin
  let _ ← oneCoin
  let _ ← oneCoin
  let _ ← oneCoin
  pure ()

/-- Four interactions cannot be charged as three by omitting the original run. -/
theorem four_queries_refute_three : fourCoins.IsTotalQueryBound 4 ∧
    ¬ fourCoins.IsTotalQueryBound 3 := by
  simp only [fourCoins,oneCoin,isTotalQueryBound_query_bind_iff]
  constructor
  · exact ⟨by decide,fun _ => ⟨by decide,fun _ => ⟨by decide,fun _ => ⟨by decide,fun _ => trivial⟩⟩⟩⟩
  · intro h
    exact Nat.not_lt_zero _ (h.2 0 |>.2 0 |>.2 0 |>.1)

/-- A uniform draw costs one even when there are no hash queries. -/
theorem uniform_query_not_free : ¬ oneCoin.IsTotalQueryBound 0 := by
  intro h
  exact Nat.not_lt_zero _ h.1

/-- The query metric assigns zero cost to every pure function; it cannot
certify the running time of local computation. -/
theorem pure_processing_uncharged (f : Nat → Nat) (n : Nat) :
    (pure (f n) : ProbComp Nat).IsTotalQueryBound 0 := trivial

#print axioms tagged_joint_four_queries
#print axioms four_queries_refute_three
#print axioms uniform_query_not_free
#print axioms pure_processing_uncharged
end ExplainableCrypto.Helios.Computational.BallotReplayCostControls
