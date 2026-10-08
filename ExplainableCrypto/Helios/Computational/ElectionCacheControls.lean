import ExplainableCrypto.Helios.Computational.ElectionCache
import ExplainableCrypto.Helios.Computational.ElectionOracleControls
import ExplainableCrypto.Helios.Computational.BallotProofProvenanceControls

/-! Finite warm-cache controls and a non-vacuous 101-element prefix bound.
The retained rejection fixture is independently derived in the original model. -/
namespace ExplainableCrypto.Helios.Computational.ElectionCacheControls
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionOracleControls (Scalar keyRequest partialRequest populated)

def statement : BallotStatement Nat := ⟨2,8,(3,13)⟩
def commitment : BallotCommitment Nat := ((16,12),(9,18))
def warm : Cache Scalar Nat := populated.cacheQuery (.ballot statement commitment) 3

theorem retained_hit :
    run (liftBallot (ballotChallengeOracle statement commitment)) warm = pure (3,warm) := by
  simp [liftBallot,ballotChallengeOracle,ballotImpl,run_ask,warm]

theorem miss_preserves_other_proofs :
    run (liftBallot (ballotChallengeOracle statement commitment)) populated =
      (do let a ← uniformSample Scalar
          pure (a,populated.cacheQuery (.ballot statement commitment) a)) := by
  simp [liftBallot,ballotChallengeOracle,ballotImpl,run_ask,ElectionOracleControls.populated,
    keyRequest,partialRequest,QueryCache.cacheQuery,ElectionOracleControls.emptyCache]

/-- Resetting a prior ballot answer changes the answer distribution itself. -/
theorem resetting_changes_answer :
    Prod.fst <$> run (liftBallot (ballotChallengeOracle statement commitment)) warm ≠
      Prod.fst <$> run (liftBallot (ballotChallengeOracle statement commitment)) populated := by
  rw [retained_hit,miss_preserves_other_proofs]
  simp only [map_pure,map_bind,bind_pure]
  intro h
  have hp := congrArg (fun oa : ProbComp Scalar => Pr[= 3 | oa]) h
  norm_num [probOutput_uniformSample,probOutput_pure] at hp
  exact (ne_of_gt (ENNReal.inv_lt_one.mpr (by norm_num : (1 : ENNReal) < 11))) hp

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩
abbrev Large := ZMod 101
noncomputable local instance : SampleableType Large := SampleableType.ofFintype Large

noncomputable def sampledPrefix := run
  (do let _ ← ask (F := Large) (.key (1 : Large) 3 4)
      samplePrefix (F := Large) (fun _ => 37) (1 : Large) false) (fun _ => none)

theorem rejection_nontrivial :
    Pr[fun out => out.1.2.2.honestDecisions ≠ (.accepted,.accepted) | sampledPrefix] ≤ 9 / 100 := by
  have hg : Function.Injective (fun r : Large => r • (1 : Large)) := by
    intro a b h; simpa [smul_eq_mul] using h
  have h := preparedPrefix_rejection_le (fun _ => 37) (1 : Large) hg false
    (ask (.key (1 : Large) 3 4)) (fun _ => none)
  norm_num [noncePointBound] at h ⊢
  exact h

theorem acceptance_positive :
    0 < Pr[fun out => out.1.2.2.honestDecisions = (.accepted,.accepted) | sampledPrefix] := by
  have hf : NeverFail sampledPrefix := inferInstance
  have hc := probEvent_compl sampledPrefix
    (fun out => out.1.2.2.honestDecisions ≠ (.accepted,.accepted))
  simp only [not_not,probFailure_eq_zero,tsub_zero] at hc
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz,add_zero] at hc
  have hn := rejection_nontrivial
  rw [hc] at hn
  exact not_le.mpr (ENNReal.div_lt_of_lt_mul (by norm_num : (9 : ENNReal) < 1 * 100)) hn

/-- The original collision fixture still rejects in the complete public prefix
under fixed-hash interpretation; acceptance is not a constant-return behavior. -/
theorem original_rejection_retained :
    let before := makeRepairedPrefix RepairControls.hashes 1 3 4 false
      ExecutionControls.aliceCoins BallotProofProvenanceControls.rejectedBobCoins
    simulateQ (functionImpl RepairControls.hashes)
      (prefixWithCoins RepairControls.hashes.fingerprint 1 3 4 false
        ExecutionControls.aliceCoins BallotProofProvenanceControls.rejectedBobCoins) = pure before ∧
      before.honestDecisions = (.accepted,.reusedCiphertext) := by
  exact ⟨prefix_function _ _ _ _ _ _ _,by decide⟩

#print axioms retained_hit
#print axioms miss_preserves_other_proofs
#print axioms resetting_changes_answer
#print axioms rejection_nontrivial
#print axioms acceptance_positive
#print axioms original_rejection_retained
end ExplainableCrypto.Helios.Computational.ElectionCacheControls
