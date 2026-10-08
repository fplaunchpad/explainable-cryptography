import ExplainableCrypto.Helios.Computational.ElectionReplaySource
import ExplainableCrypto.Helios.Computational.ElectionCacheControls
import ExplainableCrypto.Helios.Computational.BallotJointReplayControls

/-! Mixed-domain query trees plus the independent original replay controls.
The lifted positive fixture is not an arbitrary-attacker success theorem. -/
namespace ExplainableCrypto.Helios.Computational.ElectionReplayControls
open OracleComp OracleSpec ElectionOracle ElectionReplaySource
open ElectionCacheControls (statement commitment)
open ElectionOracleControls (Scalar keyRequest partialRequest)
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

def mixed : Comp Scalar Nat (List Scalar) := do
  let b ← ask (.ballot statement commitment)
  let k ← ask keyRequest
  let d ← ask partialRequest
  let k' ← ask keyRequest
  let b' ← ask (.ballot statement commitment)
  pure [b,k,d,k',b']

/-- Earlier and repeated ballot requests remain explicit. The two other proof
domains use ordinary randomness; the repeated key request keeps its answer. -/
theorem mixed_source : source mixed = (do
    let b ← ballotChallengeOracle statement commitment
    let k ← liftComp (uniformSample Scalar) (BallotOracleSpec Scalar Nat)
    let d ← liftComp (uniformSample Scalar) (BallotOracleSpec Scalar Nat)
    let b' ← ballotChallengeOracle statement commitment
    pure [b,k,d,k,b']) := by
  simp only [source,lower,mixed,ask,simulateQ_bind,simulateQ_pure,simulateQ_spec_query,
    StateT.run_bind,StateT.run_pure]
  simp [impl,auxiliary,StateT.run,keyRequest,partialRequest,
    QueryCache.cacheQuery,ballotChallengeOracle]

theorem auxiliary_hit :
    auxiliary (F := Scalar) keyRequest
      ((show Cache Scalar Nat from fun _ => none).cacheQuery keyRequest 5) =
      pure (5,(show Cache Scalar Nat from fun _ => none).cacheQuery keyRequest 5) := by
  simp [auxiliary]

theorem mixed_source_not_pure (out : List Scalar) : source mixed ≠ pure out := by
  rw [mixed_source]
  intro h
  have hp := congrArg OracleComp.isPure h
  simp only [ballotChallengeOracle,OracleComp.isPure_query_bind,OracleComp.isPure_pure,
    Bool.false_eq_true] at hp

theorem lifted_single_positive :
    0 < Pr[fun out => out.isSome |
      ElectionReplaySource.extract (liftBallot BallotForkControls.taggedProgram) Prod.snd 1] := by
  rw [ElectionReplaySource.extract,source_liftBallot]
  exact BallotForkControls.tagged_extraction_positive

theorem lifted_joint_positive :
    0 < Pr[fun out => out.isSome |
      jointExtract (liftBallot BallotForkControls.taggedProgram) (fun _ => Prod.snd) 1] := by
  rw [jointExtract,source_liftBallot]
  exact BallotJointReplayControls.tagged_joint_positive

/-- The adapter cannot turn an unqueried fixed proof into a live replay target. -/
theorem unqueried_control :
    Pr[fun x => (ballotForkSelector 0 x).isSome |
      ballotForkRunTrace (source (liftBallot BallotForkControls.fixedUnqueried))] = 0 := by
  rw [source_liftBallot]
  exact BallotForkControls.unqueried_live_only_probability_zero

#print axioms mixed_source
#print axioms auxiliary_hit
#print axioms mixed_source_not_pure
#print axioms lifted_single_positive
#print axioms lifted_joint_positive
#print axioms unqueried_control
end ExplainableCrypto.Helios.Computational.ElectionReplayControls
