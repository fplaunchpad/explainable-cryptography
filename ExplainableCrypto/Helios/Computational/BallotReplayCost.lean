import ExplainableCrypto.Helios.Computational.BallotJointReplay

/-! Oracle-interaction cost of the actual shared-path extractor. This counts
uniform draws as well as hash calls. It does not charge local computation and
therefore is not a polynomial-time certificate. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

private theorem replay_map_bound {ι α β : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (f : α → β) (m : Nat) :
    (f <$> oa).IsTotalQueryBound m ↔ oa.IsTotalQueryBound m :=
  isQueryBound_map_iff oa f m _ _

private theorem replay_path_bound {ι α : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (m : Nat) (h : oa.IsTotalQueryBound m) :
    (replayFirstPath oa).IsTotalQueryBound m := by
  exact (replay_map_bound (replayFirstPath oa) (PFunctor.FreeM.output oa) m).mp
    (by rw [map_output_replayFirstPath]; exact h)

private theorem replay_occurrence_residual_bound {ι α : Type} {spec : OracleSpec ι}
    {oa : OracleComp spec α} {i : ι} {s : Nat}
    (occ : PFunctor.FreeM.Cursor.Occurrence i oa s) (m : Nat)
    (h : oa.IsTotalQueryBound m) :
    OracleComp.IsTotalQueryBound (PFunctor.FreeM.liftBind i occ.resume : OracleComp spec α) m := by
  induction occ generalizing m with
  | here next => exact h
  | stepSame answer tail ih => exact (ih (m-1) (h.2 answer)).mono (Nat.sub_le _ _)
  | stepOther hne answer tail ih => exact (ih (m-1) (h.2 answer)).mono (Nat.sub_le _ _)

/-- Completing a physical occurrence consumes no more interactions than the
whole original program, on every answer branch. -/
theorem ballotReplay_occurrence_total_bound {ι α : Type} {spec : OracleSpec ι}
    {oa : OracleComp spec α} {i : ι} {s : Nat}
    (occ : PFunctor.FreeM.Cursor.Occurrence i oa s) (m : Nat)
    (h : oa.IsTotalQueryBound m) :
    (Cursor.completeOccurrence occ).IsTotalQueryBound m := by
  have hr := replay_occurrence_residual_bound occ m h
  change 0 < m ∧ ∀ answer, OracleComp.IsTotalQueryBound
    (occ.resume answer : OracleComp spec α) (m-1) at hr
  change 0 < m ∧ ∀ answer, OracleComp.IsTotalQueryBound
    (PFunctor.FreeM.map _ (PFunctor.FreeM.withPath (occ.resume answer)) : OracleComp spec _) (m-1)
  exact ⟨hr.1,fun answer =>
    (replay_map_bound _ _ (m-1)).mpr (replay_path_bound _ (m-1) (hr.2 answer))⟩

variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]
attribute [local implicit_reducible] ballotForkBudget

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F] in
/-- Logging forwards a uniform draw, draws once on a hash miss and returns
purely on a cache hit. Its cost is derived from the original raw source. -/
theorem ballotReplaySourceRun_total_query_bound (oa : BallotOracleComp F G A)
    (m : Nat) (h : oa.IsTotalQueryBound m) :
    (ballotReplaySourceRun oa).IsTotalQueryBound m := by
  rw [← isQueryBoundP_true_iff] at h ⊢
  apply IsQueryBoundP.simulateQ_run_StateT_of_step h
  intro t st
  cases t with
  | inl u =>
    simp only [ballotForkLoggedImpl,QueryImpl.add]
    change IsQueryBoundP (liftM ((FiatShamir.Fork.wrappedSpec F).query (.inl u)) >>= _) _ _
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨by simp,fun _ => trivial⟩
  | inr key =>
    simp only [ballotForkLoggedImpl,QueryImpl.add]
    rcases st with ⟨cache,log⟩
    cases hc : cache ((),key) with
    | none =>
      rw [FiatShamir.Fork.roImpl_run_none (M := Unit) (mc := ((),key)) (cache := cache) (log := log) hc]
      change IsQueryBoundP (liftM ((FiatShamir.Fork.wrappedSpec F).query (.inr ())) >>= _) _ _
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨by simp,fun _ => trivial⟩
    | some c =>
      rw [FiatShamir.Fork.roImpl_run_some (M := Unit) (mc := ((),key)) (cache := cache) (log := log) c hc]
      trivial

/-- A conditional attempt is either pure failure or one physical completion. -/
theorem ballotReplayAtPath_total_query_bound
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n m : Nat)
    (h : (ballotForkRunTrace oa).IsTotalQueryBound m)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace oa)) :
    (ballotReplayAtPath oa n path).IsTotalQueryBound m := by
  unfold ballotReplayAtPath
  split
  · trivial
  · split
    · trivial
    · exact (replay_map_bound _ _ m).mpr (ballotReplay_occurrence_total_bound _ m h)

/-- All three attempts run even if an earlier one fails. With m interactions
per original source branch, their conditional total is at most 3m. -/
theorem ballotJointReplayAtPath_total_query_bound
    (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n m : Nat)
    (h : (ballotReplaySourceRun oa).IsTotalQueryBound m)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    (ballotJointReplayAtPath oa select n path).IsTotalQueryBound (3*m) := by
  have hb (i : Option (Fin 2)) :
      (ballotReplaySourceAttempt oa (select i) n path).IsTotalQueryBound m := by
    unfold ballotReplaySourceAttempt
    apply (replay_map_bound _ _ m).mpr
    apply ballotReplayAtPath_total_query_bound
    rw [ballotForkRawSource_trace_eq]
    exact (replay_map_bound _ _ m).mpr h
  unfold ballotJointReplayAtPath
  rw [show 3*m = m+(m+(m+0)) by omega]
  apply isTotalQueryBound_bind (hb (some 0))
  intro w0
  apply isTotalQueryBound_bind (hb (some 1))
  intro w1
  apply isTotalQueryBound_bind (hb none)
  intro wa
  trivial

/-- One original execution plus three residual completions costs at most 4m
oracle interactions. Pure processing and encoded response sizes remain separate. -/
theorem ballotJointReplay_total_query_bound
    (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n m : Nat)
    (h : oa.IsTotalQueryBound m) :
    (ballotJointReplay oa select n).IsTotalQueryBound (4*m) := by
  have hr := ballotReplaySourceRun_total_query_bound oa m h
  unfold ballotJointReplay
  rw [show 4*m = m+3*m by omega]
  apply isTotalQueryBound_bind (replay_path_bound _ m hr)
  intro path
  exact (replay_map_bound _ _ (3*m)).mpr
    (ballotJointReplayAtPath_total_query_bound oa select n m hr path)

#print axioms ballotReplaySourceRun_total_query_bound
#print axioms ballotReplay_occurrence_total_bound
#print axioms ballotReplayAtPath_total_query_bound
#print axioms ballotJointReplayAtPath_total_query_bound
#print axioms ballotJointReplay_total_query_bound
end ExplainableCrypto.Helios.Computational
