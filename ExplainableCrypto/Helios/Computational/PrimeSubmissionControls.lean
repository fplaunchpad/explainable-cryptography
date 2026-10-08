import ExplainableCrypto.Helios.Computational.PrimeSubmission
import ExplainableCrypto.Helios.Computational.BallotFiniteProgrammedControls

/-! Actual nonce execution must preserve prior cache and collision state. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSubmissionControls
open OracleComp OracleSpec BallotFiniteProgrammedControls
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The actual sampler retains a preexisting collision, duplicate history and
both cached answers. No fresh-state premise erases these observations. -/
theorem nonce_state_retained
    (out : ((Scalar × Scalar) × BallotFiniteProgrammedState Scalar Scalar) × BallotFiniteCache Scalar Scalar)
    (ho : out ∈ support (runBallotFiniteCache
      ((simulateQ (ballotFiniteProgrammedImpl (1 : Scalar) 2)
        (liftComp (drawPrimeNoncePair (q := 11)) (BallotProofOracleSpec Scalar Scalar))).run collision)
      first.cache)) :
    out.1.2.bad = true ∧ out.1.2.programmed = [stmt0,stmt0] ∧
    out.1.2.cache.lookup (stmt0,(transcript 0).1) = some 0 ∧
    out.2.lookup (stmt0,(transcript 0).1) = some 0 := by
  rw [drawPrimeNoncePair_finite_state,support_map] at ho
  obtain ⟨rs,_,rfl⟩ := ho
  dsimp only
  decide

/-- Starting the same actual nonce sampler with empty state has no collision;
resetting the previous control's state would change its retained observation. -/
theorem empty_nonce_state
    (out : ((Scalar × Scalar) × BallotFiniteProgrammedState Scalar Scalar) × BallotFiniteCache Scalar Scalar)
    (ho : out ∈ support (runBallotFiniteCache
      ((simulateQ (ballotFiniteProgrammedImpl (1 : Scalar) 2)
        (liftComp (drawPrimeNoncePair (q := 11)) (BallotProofOracleSpec Scalar Scalar))).run .empty)
      ∅)) : out.1.2.bad = false ∧ out.1.2.programmed = [] := by
  rw [drawPrimeNoncePair_finite_state,support_map] at ho
  obtain ⟨rs,_,rfl⟩ := ho
  exact ⟨rfl,rfl⟩

#print axioms nonce_state_retained
#print axioms empty_nonce_state
end ExplainableCrypto.Helios.Computational.PrimeSubmissionControls
