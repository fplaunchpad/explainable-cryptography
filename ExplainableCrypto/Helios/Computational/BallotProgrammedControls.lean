import ExplainableCrypto.Helios.Computational.BallotProgrammedOracle
import ExplainableCrypto.Helios.Computational.AdaptiveBallotControls

/-! Positive and negative controls for replayable programming. These use the
independently derived p=23/q=11 commitments and the original full proofs. -/
namespace ExplainableCrypto.Helios.Computational.BallotProgrammedControls
open OracleComp OracleSpec StrongBallotOracleControls AdaptiveBallotControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def freshState : BallotProgrammedState Scalar Scalar := ⟨cached 5,false,[stmt]⟩
def collisionState : BallotProgrammedState Scalar Scalar := ⟨cached 6,true,[stmt]⟩

private theorem request_run (wit : Bool × Scalar)
    (s : BallotProgrammedState Scalar Scalar) (live : BallotOracleCache Scalar Scalar) :
    runBallotOracle (((ballotProgrammedImpl (F := Scalar) 1 3) (.inr wit)).run s) live =
      (fun out => ((out.1.1,(⟨out.2,s.bad || out.1.2,
        honestProofStatement 1 3 wit :: s.programmed⟩ : BallotProgrammedState Scalar Scalar)),live))
        <$> (strongBallotSimOracle (honestProofStatement 1 3 wit)).run s.cache := by
  change runBallotOracle (do
    let out ← liftComp ((strongBallotSimOracle (F := Scalar)
      (honestProofStatement 1 3 wit)).run s.cache) (BallotOracleSpec Scalar Scalar)
    pure (out.1.1,(⟨out.2,s.bad || out.1.2,
      honestProofStatement 1 3 wit :: s.programmed⟩ : BallotProgrammedState Scalar Scalar))) live = _
  rw [runBallotOracle_lift_bind]
  simp [runBallotOracle]

theorem fresh_request_reachable :
    ((proof,freshState),∅) ∈ support
      (runBallotProgrammed 1 3 (ballotProofQuery (false,(3 : Scalar)))) := by
  have he : honestProofStatement (1 : Scalar) 3 (false,(3 : Scalar)) = stmt := by decide
  simp only [runBallotProgrammed,ballotProofQuery,simulateQ_spec_query]
  rw [request_run]
  rw [support_map]
  refine ⟨((proof,false),cached 5), ?_, ?_⟩
  · simpa only [he,BallotProgrammedState.empty] using fresh_simulation_possible
  · simp [he,BallotProgrammedState.empty,freshState]

/-- The programmed answer is returned without putting that point in the live cache. -/
theorem programmed_hit_preserves_live :
    runBallotOracle ((ballotProgrammedRaw (F := Scalar) (G := Scalar)
      (.inr (stmt,pc))).run freshState) ∅ = pure (((5 : Scalar),freshState),∅) := by
  have h : ((ballotProgrammedRaw (F := Scalar) (G := Scalar)
      (.inr (stmt,pc))).run freshState) = pure ((5 : Scalar),freshState) := by
    simp [ballotProgrammedRaw,QueryImpl.add,StateT.run,freshState,cached]
  rw [h]
  simp [runBallotOracle]

theorem conflicting_request_preserves_live :
    ((proof,collisionState),cached 6) ∈ support
      (runBallotOracle (((ballotProgrammedImpl (F := Scalar) 1 3)
        (.inr (false,(3 : Scalar)))).run ⟨cached 6,false,[]⟩) (cached 6)) := by
  rw [request_run]
  rw [support_map]
  have he : honestProofStatement (1 : Scalar) 3 (false,(3 : Scalar)) = stmt := by decide
  refine ⟨((proof,true),cached 6), ?_, ?_⟩
  · simpa only [he] using conflicting_simulation_flagged_and_preserved
  · simp [he,collisionState]

theorem fresh_after_collision_still_flagged :
    ((freshProof,(⟨(cached 6).cacheQuery (freshStmt,freshPC) 5,true,
      [freshStmt,stmt]⟩ : BallotProgrammedState Scalar Scalar)),cached 6) ∈ support
      (runBallotOracle (((ballotProgrammedImpl (F := Scalar) 1 3)
        (.inr (true,(4 : Scalar)))).run collisionState) (cached 6)) := by
  rw [request_run]
  have h := fresh_after_collision_keeps_flag
  rw [runBallotProofSim_request] at h
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at h
  obtain ⟨out,ho,he⟩ := h
  rw [support_map]
  refine ⟨out,ho,?_⟩
  have hp := congrArg Prod.fst he
  have hc := congrArg (fun x => x.2.1) he
  dsimp only at hp hc
  simp only [collisionState,Bool.true_or,← hp,← hc]
  rfl

/-- Dropping statement exclusion permits different verification outcomes. -/
theorem programmed_target_can_disagree :
    runBallotOracle (strongBallotVerifyOracle stmt proof) freshState.cache =
      pure (true,freshState.cache) ∧
    false ∈ support (Prod.fst <$> runBallotOracle (strongBallotVerifyOracle stmt proof) ∅) := by
  constructor
  · exact fresh_simulation_verifies
  · simp only [runBallotOracle,strongBallotVerifyOracle,simulateQ_bind,
      simulateQ_pure,StateT.run_bind,StateT.run_pure]
    rw [← runBallotOracle,runBallotOracle_query]
    simp only [QueryCache.empty_apply,bind_pure_comp,Functor.map_map,
      support_map,Set.mem_image]
    refine ⟨6,by simp,?_⟩
    decide

/-- Erasing the requested statement loses the justified cache-agreement invariant. -/
theorem clearing_provenance_breaks_invariant :
    ¬ BallotProgrammedInv {freshState with programmed := []} ∅ := by
  intro h
  have he := h.2 (stmt,pc) (by simp)
  simp [freshState,cached] at he

/-- Arbitrary initial caches cannot replace the derived empty-state invariant. -/
theorem inconsistent_initial_caches :
    ¬ BallotProgrammedInv (BallotProgrammedState.empty : BallotProgrammedState Scalar Scalar)
      (cached 6) := by
  intro h
  have he := h.1 (show cached 6 (stmt,pc) = some 6 by simp [cached])
  simp [BallotProgrammedState.empty] at he

theorem adaptive_runtime_exact :
    (fun out => (out.1.1,out.1.2.toSimState)) <$> runBallotProgrammed 1 3 adaptiveTwoProofs =
      runBallotProofSim 1 3 adaptiveTwoProofs (∅,false) :=
  ballotProgrammed_runtime_eq 1 3 adaptiveTwoProofs

theorem adaptive_live_query_bound :
    ((simulateQ (ballotProgrammedImpl (F := Scalar) 1 3) adaptiveTwoProofs).run .empty).IsQueryBoundP (isBallotHashQuery (F := Scalar)) 2 :=
  ballotProgrammed_query_bound 1 3 adaptiveTwoProofs 2
    (by simp [adaptiveTwoProofs,ballotProofQuery,growsBallotCache]) .empty

#print axioms fresh_request_reachable
#print axioms programmed_hit_preserves_live
#print axioms conflicting_request_preserves_live
#print axioms fresh_after_collision_still_flagged
#print axioms programmed_target_can_disagree
#print axioms clearing_provenance_breaks_invariant
#print axioms inconsistent_initial_caches
#print axioms adaptive_runtime_exact
#print axioms adaptive_live_query_bound
end ExplainableCrypto.Helios.Computational.BallotProgrammedControls
