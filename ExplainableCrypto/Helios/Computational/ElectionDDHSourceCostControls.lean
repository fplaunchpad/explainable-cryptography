import ExplainableCrypto.Helios.Computational.ElectionDDHSourceCost
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls

/-! Actual source-cost instances and controls against omitting random draws or
auxiliary misses. Uniform-index costs remain distinct from bit costs. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSourceCostControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩

private theorem prepare_total : prepare.IsTotalQueryBound 2 := by
  exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩

private theorem cast_total (b : Ballot Scalar Scalar 2) (initial : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b initial).castBallot before).IsTotalQueryBound 1 := by
  exact ⟨by norm_num,fun _ => trivial⟩

private theorem guess_total (b : Ballot Scalar Scalar 2) (initial : Scalar × Scalar)
    (saved : Scalar) (view : PublicResult Scalar Scalar) :
    ((adversary b initial).guessVote saved view).IsTotalQueryBound 1 := by
  exact ⟨by norm_num,fun _ => trivial⟩

/-- The actual querying prefix has a derived conservative budget of 90,
including coins and both auxiliary and ballot queries. -/
theorem prefix_after_queries (b : Ballot Scalar Scalar 2) :
    (prefixSource (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b)).IsTotalQueryBound 90 :=
  prefix_total_bound _ _ _ _ _ _ _ 2 1 primeScalarSampler_total_bound prepare_total (cast_total b)

/-- Include the original, all repeated residuals, final trustee proofs and the
saved-state-dependent guess. The prime sampler cost is derived by the theorem. -/
theorem complete_after_queries (b : Ballot Scalar Scalar 2) (k : Nat) :
    (extractedGame (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b) 10 k).IsTotalQueryBound
      ((1+3*k)*90+8) :=
  extractedGame_prime_total_bound _ _ _ _ _ _ _ 10 k 2 1 1 prepare_total (cast_total b) (guess_total b)

/-- No live ballot hash is issued, but an auxiliary miss still draws a scalar. -/
theorem auxiliary_miss_cost :
    (ask (F := Scalar) key).IsQueryBoundP (ElectionQueryBound.isBallot (F := Scalar)) 0 ∧
    ¬ (ElectionReplaySource.auxiliary (F := Scalar) key ∅).IsTotalQueryBound 0 := by
  constructor
  · simp [ask,key,ElectionQueryBound.isBallot]
  · change ¬ ((0 : Nat) > 0 ∧ _)
    simp

/-- A cached answer incurs no new oracle draw; misses cannot be treated as hits. -/
theorem auxiliary_hit_cost :
    (ElectionReplaySource.auxiliary (F := Scalar) key
      ((∅ : Cache Scalar Scalar).cacheQuery key 7)).IsTotalQueryBound 0 := by
  simp only [ElectionReplaySource.auxiliary,QueryCache.cacheQuery]
  trivial

/-- A discarded private draw still costs an interaction, even though it leaves
the subsequent fair output distribution unchanged. -/
theorem discarded_draw_cost :
    (do let _ ← uniformSample Bool; uniformSample Bool).IsTotalQueryBound 2 ∧
    ¬ (do let _ ← uniformSample Bool; uniformSample Bool).IsTotalQueryBound 1 := by
  constructor
  · exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩
  · intro h
    have hn := (h.2 0).1
    norm_num at hn

#print axioms prefix_after_queries
#print axioms complete_after_queries
#print axioms auxiliary_miss_cost
#print axioms auxiliary_hit_cost
#print axioms discarded_draw_cost
end ExplainableCrypto.Helios.Computational.ElectionDDHSourceCostControls
