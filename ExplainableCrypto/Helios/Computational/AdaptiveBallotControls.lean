import ExplainableCrypto.Helios.Computational.AdaptiveBallotSimulation
import ExplainableCrypto.Helios.Computational.StrongBallotOracleControls

/-! Controls for adaptive requests, cache accounting and sticky collision flags.
Expected multiplicative coordinates are independently derived modulo 23. -/
namespace ExplainableCrypto.Helios.Computational.AdaptiveBallotControls

open OracleComp OracleSpec StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def adaptiveTwoProofs : OracleComp (BallotProofOracleSpec Scalar Scalar)
    (Proof01 Scalar Scalar × Proof01 Scalar Scalar) := do
  let first ← ballotProofQuery (false,(3 : Scalar))
  let second ← ballotProofQuery (if first.zero.challenge = 0 then (true,4) else (false,3))
  pure (first,second)

theorem adaptive_two_proofs_distance_le :
    tvDist (runBallotProofReal 1 3 adaptiveTwoProofs (∅,false))
      (runBallotProofSim 1 3 adaptiveTwoProofs (∅,false)) ≤ 10 / 11 := by
  have hg : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
    intro a b h
    simpa [smul_eq_mul] using h
  have hn : adaptiveTwoProofs.IsQueryBoundP growsBallotCache 2 := by
    simp [adaptiveTwoProofs, ballotProofQuery, growsBallotCache]
  have hp : adaptiveTwoProofs.IsQueryBoundP isBallotProofRequest 2 := by
    simp [adaptiveTwoProofs, ballotProofQuery, isBallotProofRequest]
  have h := strongBallot_programming_distance_le 1 3 hg adaptiveTwoProofs 2 2 0 hn hp
    (∅,false) BallotCacheBound.empty
  norm_num at h ⊢
  exact h

def hashOnly : OracleComp (BallotProofOracleSpec Scalar Scalar) Scalar :=
  liftM ((BallotProofOracleSpec Scalar Scalar).query (.inl (.inr (stmt,pc))))

theorem hash_only_exact :
    𝒮[runBallotProofReal 1 3 hashOnly (∅,false)] =
      𝒮[runBallotProofSim 1 3 hashOnly (∅,false)] := by
  have hg : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
    intro a b h
    simpa [smul_eq_mul] using h
  have h := strongBallot_programming_distance_le 1 3 hg hashOnly 1 0 0
    (by simp [hashOnly,growsBallotCache]) (by simp [hashOnly,isBallotProofRequest])
    (∅,false) BallotCacheBound.empty
  simp only [Nat.cast_zero, zero_mul] at h
  exact (tvDist_eq_zero_iff _ _).mp (le_antisymm h (tvDist_nonneg _ _))

theorem initial_cache_has_budget_one : BallotCacheBound (cached 6) 1 :=
  BallotCacheBound.empty.cacheQuery _ _

theorem initial_cache_cannot_be_ignored : ¬ BallotCacheBound (cached 6) 0 := by
  rintro ⟨Q,hQ,hcov⟩
  have hQ0 : Q = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hQ)
  have h := hcov (stmt,pc) (by simp [cached])
  simp [hQ0] at h

theorem collision_request_retains_flag :
    (proof,(cached 6,true)) ∈ support
      (runBallotProofSim 1 3 (ballotProofQuery (false,(3 : Scalar))) (cached 6,false)) := by
  rw [runBallotProofSim_request]
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
  refine ⟨((proof,true),cached 6), ?_, rfl⟩
  have he : honestProofStatement (1 : Scalar) 3 (false,(3 : Scalar)) = stmt := by decide
  rw [he]
  exact conflicting_simulation_flagged_and_preserved

def freshStmt : BallotStatement Scalar := honestProofStatement 1 3 (true,(4 : Scalar))
def freshPC : BallotCommitment Scalar := ballotSimCommit freshStmt (5 : Scalar) (2,3,4)
def freshProof : Proof01 Scalar Scalar := ballotTranscriptProof freshPC 5 (2,3,4)

theorem fresh_commitment_fixture :
    ((ExecutionControls.encode freshPC.1.1,ExecutionControls.encode freshPC.1.2),
      (ExecutionControls.encode freshPC.2.1,ExecutionControls.encode freshPC.2.2)) =
      ((18,9),(8,6)) := by decide

theorem fresh_after_collision_keeps_flag :
    (freshProof,((cached 6).cacheQuery (freshStmt,freshPC) 5,true)) ∈ support
      (runBallotProofSim 1 3 (ballotProofQuery (true,(4 : Scalar))) (cached 6,true)) := by
  rw [runBallotProofSim_request]
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
  refine ⟨((freshProof,false),(cached 6).cacheQuery (freshStmt,freshPC) 5), ?_, rfl⟩
  change _ ∈ support ((strongBallotSimOracle (F := Scalar) freshStmt).run (cached 6))
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion]
  refine ⟨(freshPC,5,(2,3,4)), ?_, ?_⟩
  · simp only [ballotFullSimTranscript, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨5,by simp,2,by simp,3,by simp,4,by simp,rfl⟩
  · have hf : cached 6 (freshStmt,freshPC) = none := by decide
    simp [hf,freshProof]

theorem resetting_flag_is_impossible (p : Proof01 Scalar Scalar)
    (cache : BallotOracleCache Scalar Scalar) :
    (p,(cache,false)) ∉ support
      (runBallotProofSim 1 3 (ballotProofQuery (true,(4 : Scalar))) (cached 6,true)) := by
  intro h
  have he := runBallotProofSim_flag_sticky 1 3 _ (cached 6,true) rfl (p,(cache,false)) h
  exact Bool.false_ne_true he

#print axioms adaptive_two_proofs_distance_le
#print axioms hash_only_exact
#print axioms initial_cache_has_budget_one
#print axioms initial_cache_cannot_be_ignored
#print axioms collision_request_retains_flag
#print axioms fresh_commitment_fixture
#print axioms fresh_after_collision_keeps_flag
#print axioms resetting_flag_is_impossible

end ExplainableCrypto.Helios.Computational.AdaptiveBallotControls
