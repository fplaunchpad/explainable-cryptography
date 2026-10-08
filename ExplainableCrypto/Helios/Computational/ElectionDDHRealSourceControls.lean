import ExplainableCrypto.Helios.Computational.ElectionDDHRealSource
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls

/-! Actual querying-game, key-loss and rejection controls. Field 257 is a
finite arithmetic fixture, not a hardness assumption. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHRealSourceControls
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
-- Keep the constructor-name linter from evaluating complete finite oracle trees
-- while inspecting support hypotheses. The proofs use their checked interfaces.
attribute [local irreducible] sampleNonzero ElectionProgrammedSource.evaluate

private theorem prepare_bound : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 2 := by
  simp [prepare,ask,key,ElectionCacheBudget.isHash]

private theorem cast_bound (b : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b remembered).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := Scalar)) 1 := by
  simp [adversary,ask,ElectionCacheBudget.isHash]

private theorem generator_injective : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
  intro a b h
  simpa [smul_eq_mul] using h

/-- Querying preparation, saved-state-dependent casting and the actual guessing
callback remain present in the complete real-challenge comparison. -/
theorem complete_comparison (b : Ballot Scalar Scalar 2) :
    tvDist ((fun out => ((out.1,false),out.2)) <$>
      run (ElectionExtraction.preparedSource (fun p => p.trusteeKeyProof.response.val) 1 prepare (adversary b)) ∅)
      (ElectionProgrammedSource.result <$>
        realGame (fun p => p.trusteeKeyProof.response.val) 1 prepare (adversary b)) ≤ (155/257 : ℝ) := by
  have h := prepared_real_distance_le (fun p => p.trusteeKeyProof.response.val) 1 generator_injective
    prepare (adversary b) 2 1 prepare_bound (cast_bound b)
  norm_num at h ⊢
  exact h

/-- The actual comparison allowance is strictly below one. -/
theorem comparison_nonvacuous : (155/257 : ℝ) < 1 := by norm_num

/-- Uniform DDH key sampling admits zero with mass 1/257; the historical key
sampler rejects it. The extra key term cannot be silently dropped. -/
theorem key_sampling_differs :
    Pr[= (0 : Scalar) | uniformSample Scalar] = 1/257 ∧
    Pr[= (0 : Scalar) | sampleNonzero Scalar] = 0 := by
  constructor
  · norm_num [probOutput_uniformSample]
  · exact probOutput_eq_zero_of_not_mem_support (fun h => sampleNonzero_ne_zero h rfl)

private def priorState : ElectionProgrammedSource.State Scalar Scalar :=
  ⟨(∅ : Cache Scalar Scalar).cacheQuery key 5,true,[statement]⟩
private def priorLive : BallotOracleCache Scalar Scalar :=
  (∅ : BallotOracleCache Scalar Scalar).cacheQuery (statement,commitment) 7

/-- Randomness preserves the complete nonempty source and live states, including
a preexisting flag and recorded target. No consistency premise is required. -/
theorem random_draw_preserves_state :
    ElectionProgrammedSource.evaluate (ElectionProgrammedSource.raw 1 3 (liftProb (uniformSample Bool)))
      priorState priorLive = (fun bit => ((bit,priorState),priorLive)) <$> uniformSample Bool :=
  raw_prob 1 3 _ _ _

/-- Resetting the retained live cache would destroy this existing answer. -/
theorem reset_loses_answer : priorLive (statement,commitment) = some 7 ∧
    (∅ : BallotOracleCache Scalar Scalar) (statement,commitment) = none := by
  simp [priorLive]

/-- Invalid-proof rejection and the retained board survive proof publication
and the actual subsequent querying callback. -/
theorem rejected_finish (before : PublicPrefix Scalar Scalar) (b : Ballot Scalar Scalar 2)
    (board : List (BoardEntry Scalar Scalar)) (remembered : Scalar × Scalar) (saved : Scalar)
    (out : ((PublicResult Scalar Scalar × Bool) × ElectionProgrammedSource.State Scalar Scalar) ×
      BallotOracleCache Scalar Scalar)
    (ho : out ∈ support (ElectionProgrammedSource.evaluate
      (finishAfterCast 1 3 3 (adversary b remembered) true before b saved (.invalidProof,board))
        priorState priorLive)) :
    out.1.1.1.decision = .invalidProof ∧ out.1.1.1.board = board ∧
      out.1.1.1.encryptedTally = boardTally board := by
  with_reducible
    have h := finishAfterCast_publication 1 3 3 (adversary b remembered) true before b saved
      (.invalidProof,board) priorState priorLive out ho
    exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

#print axioms complete_comparison
#print axioms comparison_nonvacuous
#print axioms key_sampling_differs
#print axioms random_draw_preserves_state
#print axioms reset_loses_answer
#print axioms rejected_finish
end ExplainableCrypto.Helios.Computational.ElectionDDHRealSourceControls
