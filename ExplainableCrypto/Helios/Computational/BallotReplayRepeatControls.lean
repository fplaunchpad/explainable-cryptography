import ExplainableCrypto.Helios.Computational.ElectionDDHPrefixRepeat
import ExplainableCrypto.Helios.Computational.ElectionDDHPrefixControls

/-! Exact finite positive/negative repetition controls and an instantiation of
the actual challenge prefix. Finite fields here carry no hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.BallotReplayRepeatControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls

private def fairAttempt : ProbComp (Option Unit) := do
  let b ← uniformSample Bool
  pure (if b then some () else none)

private theorem fair_failure : Pr[= none | fairAttempt] = 1/2 := by
  simp only [fairAttempt,bind_pure_comp,probOutput_map]
  norm_num [probEvent_eq_tsum_ite,tsum_fintype,probOutput_uniformSample,Option.some_ne_none]

/-- Two fresh residual draws square the one-half failure mass. -/
theorem two_attempts : Pr[= none | replayRepeat fairAttempt 2] = 1/4 := by
  rw [replayRepeat_failure,fair_failure]
  simp only [one_div,← ENNReal.inv_pow]
  norm_num

/-- Reusing the first random choice fails with one-half probability, so it is
not the independent two-attempt experiment. -/
theorem reused_randomness_fails :
    Pr[= none | fairAttempt] ≠ Pr[= none | replayRepeat fairAttempt 2] := by
  rw [fair_failure,two_attempts]
  norm_num

/-- Zero trials return failure even when an attempted replay would always work. -/
theorem zero_attempts :
    replayRepeat (pure (some true) : ProbComp (Option Bool)) 0 = pure none ∧
    replayRepeat (pure (some true) : ProbComp (Option Bool)) 1 = pure (some true) := by
  simp [replayRepeat]

private def retainedTag (k : Nat) : ProbComp (Bool × Option Unit) := do
  let first ← uniformSample Bool
  let w ← replayRepeat (pure (if first then some () else none)) k
  pure (first,w)

/-- A never-extractable original tag keeps its original half of the output mass. -/
theorem original_tag_preserved : Pr[fun out => out.1 = false | retainedTag 2] = 1/2 := by
  norm_num [retainedTag,replayRepeat,probEvent_bind_eq_tsum,tsum_fintype,probOutput_uniformSample]

private def resampledOriginal : ProbComp (Option Bool) := do
  let first ← uniformSample Bool
  pure (if first then some first else none)

/-- Resampling the original on failure changes its true-tag mass from 1/2 to
3/4. This checked mutant excludes that tempting replacement algorithm. -/
theorem resampling_bias :
    Pr[= some true | replayRepeat resampledOriginal 2] = 3/4 := by
  norm_num [replayRepeat,resampledOriginal,probOutput_bind_eq_tsum,tsum_fintype,probOutput_uniformSample]
  simp only [Option.some_ne_none,ite_false,add_zero]
  have hn : (1/2 : NNReal)+(1/2)*(1/2) = 3/4 := by norm_num
  simpa [ENNReal.coe_div] using
    congrArg (fun x : NNReal => (x : ENNReal)) hn

local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

private theorem prepare_bound : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := Scalar)) 1 := by
  simp [prepare,ask,key,ElectionQueryBound.isBallot]

private theorem cast_bound (b : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b remembered).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := Scalar)) 0 := by
  simp [adversary,ask,key,ElectionQueryBound.isBallot]

/-- The actual non-DH querying prefix has the stated accepted-failure bound for
every finite repetition count; no source validity premise is supplied. -/
theorem prefix_failure_after_queries (b : Ballot Scalar Scalar 2) (k : Nat) (δ : ENNReal) :
    Pr[fun out => PrefixAccepted out.1.1 ∧ out.2 = none |
      prefixRepeated (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b) 10 k] ≤
      33*δ + (1-(δ-1/257)^3)^k := by
  have h := prefix_failure_le (fun p => p.trusteeKeyProof.response.val) 1 3 2 7
    (by decide +kernel : (1 : Scalar) ≠ 0) prepare (adversary b) 1 0 k prepare_bound (cast_bound b) δ
  norm_num at h ⊢
  exact h

/-- Regardless of success, the complete original state and live cache have the
actual querying prefix distribution. -/
theorem prefix_original_after_queries (b : Ballot Scalar Scalar 2) (k : Nat) :
    evalSPMF (Prod.fst <$> prefixRepeated (fun p => p.trusteeKeyProof.response.val)
      1 3 2 7 prepare (adversary b) 10 k) =
    evalSPMF (runBallotOracle (prefixSource (fun p => p.trusteeKeyProof.response.val)
      1 3 2 7 prepare (adversary b)) ∅) :=
  prefix_repeated_original _ _ _ _ _ _ _ _ _

#print axioms two_attempts
#print axioms reused_randomness_fails
#print axioms zero_attempts
#print axioms original_tag_preserved
#print axioms resampling_bias
#print axioms prefix_failure_after_queries
#print axioms prefix_original_after_queries
end ExplainableCrypto.Helios.Computational.BallotReplayRepeatControls
