import ExplainableCrypto.Helios.Computational.BallotJointReplayBound
import ExplainableCrypto.Helios.Computational.BallotReplayCost

/-! Finite residual repetition. The caller supplies one fixed original path;
repetition never samples another original or filters the retained output. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

/-- Repeat a residual computation at most k times, stopping at its first witness.
The computation itself closes over the already chosen original path. -/
def replayRepeat {ι B : Type} {spec : OracleSpec ι}
    (attempt : OracleComp spec (Option B)) : Nat → OracleComp spec (Option B)
  | 0 => pure none
  | k+1 => do
    match ← attempt with
    | none => replayRepeat attempt k
    | some w => pure (some w)

/-- Repetition can only return witnesses supported by the original residual
attempt; no new witness or new original path is manufactured. -/
theorem replayRepeat_supported {ι B : Type} {spec : OracleSpec ι}
    (attempt : OracleComp spec (Option B)) (k : Nat) (w : B)
    (h : some w ∈ support (replayRepeat attempt k)) : some w ∈ support attempt := by
  induction k with
  | zero => simp [replayRepeat] at h
  | succ k ih =>
    rw [replayRepeat,mem_support_bind_iff] at h
    obtain ⟨out,ho,hr⟩ := h
    cases out with
    | none => exact ih hr
    | some v =>
      simp only [mem_support_pure_iff,Option.some.injEq] at hr
      subst v
      exact ho

/-- At most k residual runs: every counted query in the attempt is included.
This structural bound does not claim a machine runtime certificate. -/
theorem replayRepeat_bound {ι B : Type} {spec : OracleSpec ι}
    (attempt : OracleComp spec (Option B)) (p : ι → Prop) [DecidablePred p]
    (n k : Nat) (h : attempt.IsQueryBoundP p n) :
    (replayRepeat attempt k).IsQueryBoundP p (k*n) := by
  induction k with
  | zero => simp [replayRepeat]
  | succ k ih =>
    rw [Nat.succ_mul,add_comm (k*n) n]
    simp only [replayRepeat]
    apply isQueryBoundP_bind h
    intro out _
    cases out with
    | none => exact ih
    | some v => simp

section Probability
variable {ι B : Type} {spec : OracleSpec ι} [IsProbabilitySpec spec]

/-- Exact geometric failure law of the actual finite loop. -/
theorem replayRepeat_failure (attempt : OracleComp spec (Option B)) (k : Nat) :
    Pr[= none | replayRepeat attempt k] = Pr[= none | attempt]^k := by
  classical
  induction k with
  | zero => simp [replayRepeat]
  | succ k ih =>
    rw [replayRepeat,probOutput_bind_eq_tsum]
    rw [tsum_eq_single none]
    · simp only [ih,pow_succ,mul_comm]
    · intro out hne
      cases out with
      | none => exact (hne rfl).elim
      | some v => simp
end Probability

variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

/-- Every repetition resumes from this same supplied path. -/
def ballotJointReplayRepeatAtPath (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :=
  replayRepeat (ballotJointReplayAtPath oa select n path) k

/-- Retain the actual original output and live cache on both success and failure.
Residual replay caches do not replace this cache. -/
def ballotJointReplayRetained (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat) := do
  let path ← replayFirstPath (ballotReplaySourceRun oa)
  let w ← ballotJointReplayRepeatAtPath oa select n k path
  let raw := PFunctor.FreeM.output _ path
  pure ((raw.1,ballotForkCacheProject raw.2.1),w)


/-- One original run plus at most 3k residual completions. The budget counts all
oracle interactions, including private randomness, but not pure local work. -/
theorem ballotJointReplayRetained_total_query_bound (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k m : Nat)
    (hm : oa.IsTotalQueryBound m) :
    (ballotJointReplayRetained oa select n k).IsTotalQueryBound ((1+3*k)*m) := by
  have map_bound {ι B C : Type} {spec : OracleSpec ι}
      (oa : OracleComp spec B) (f : B → C) (m : Nat) :
      (f <$> oa).IsTotalQueryBound m ↔ oa.IsTotalQueryBound m :=
    isQueryBound_map_iff oa f m _ _
  have hr := ballotReplaySourceRun_total_query_bound oa m hm
  have hp : (replayFirstPath (ballotReplaySourceRun oa)).IsTotalQueryBound m := by
    exact (map_bound (replayFirstPath (ballotReplaySourceRun oa)) (PFunctor.FreeM.output _) m).mp
      (by rw [map_output_replayFirstPath]; exact hr)
  unfold ballotJointReplayRetained
  rw [show (1+3*k)*m = m+k*(3*m) by ring]
  apply isTotalQueryBound_bind hp
  intro path
  rw [bind_pure_comp]
  apply (map_bound _ _ _).mpr
  rw [← isQueryBoundP_true_iff]
  apply replayRepeat_bound
  rw [isQueryBoundP_true_iff]
  exact ballotJointReplayAtPath_total_query_bound oa select n m hr path

section Finite
variable [Fintype F]
local instance replayRepeatInhabited : Inhabited F := ⟨0⟩
noncomputable local instance replayRepeatUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- There is no missing probability mass in the residual loop. -/
theorem ballotJointReplayRepeatAtPath_lossless (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    Pr[⊥ | ballotJointReplayRepeatAtPath oa select n k path] = 0 :=
  probFailure_of_liftM_PMF _

/-- Conditional geometric failure outside the charged low-context event. -/
theorem ballotJointReplayRepeatAtPath_failure_le (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat) (δ : ENNReal)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa))
    (hs : ∀ i, (ballotForkSelector n (PFunctor.FreeM.output _
      (ballotReplaySourcePath oa (select i) path))).isSome)
    (hg : ¬ ballotJointReplayBadContext oa select n δ path) :
    Pr[= none | ballotJointReplayRepeatAtPath oa select n k path] ≤
      (1-(δ-(Fintype.card F : ENNReal)⁻¹)^3)^k := by
  rw [ballotJointReplayRepeatAtPath,replayRepeat_failure]
  apply pow_le_pow_left'
  have h := ballotJointReplayAtPath_threshold_le oa select n δ path hs hg
  have hc := probEvent_compl (ballotJointReplayAtPath oa select n path) (fun out => out.isSome)
  have he : (fun out : Option (Option (Fin 2) → BallotWitness F) => ¬ out.isSome) =
      (fun out => out = none) := by funext out; cases out <;> simp
  rw [he] at hc
  have hn : Pr[= none | ballotJointReplayAtPath oa select n path] ≤
      1-Pr[fun out => out.isSome | ballotJointReplayAtPath oa select n path] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    simpa only [probEvent_eq_eq_probOutput] using hc.le.trans (tsub_le_self : (1 : ENNReal)-_ ≤ 1)
  exact hn.trans (tsub_le_tsub_left h 1)

/-- Success yields valid witnesses for the retained original output, whose exact
returned live cache belongs to an actual runtime of the source. -/
theorem ballotJointReplayRetained_valid (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat)
    (out : A × BallotOracleCache F G) (w : Option (Fin 2) → BallotWitness F)
    (ho : (out,some w) ∈ support (ballotJointReplayRetained oa select n k)) :
    out ∈ support (runBallotOracle oa ∅) ∧
    ∀ i, (select i out.1).1.Witnesses (w i) ∧ ∃ c : F,
      (select i out.1).2.Valid (fun _ => c) (select i out.1).1.generator
        (select i out.1).1.publicKey (select i out.1).1.ciphertext := by
  simp only [ballotJointReplayRetained,mem_support_bind_iff,mem_support_pure_iff] at ho
  obtain ⟨path,_,ow,hw,he⟩ := ho
  obtain ⟨hout,how⟩ := Prod.mk.inj he
  subst out
  subst ow
  refine ⟨ballotReplaySourcePath_runtime_mem oa path,?_⟩
  have hj := replayRepeat_supported (ballotJointReplayAtPath oa select n path) k w hw
  intro i
  exact ballotReplaySourceAttempt_valid oa (select i) n path (w i)
    (ballotJointReplayAtPath_supported oa select n path w hj i)

/-- Averaging over the original path charges low contexts once, then the
geometric residual failure. Acceptance refers to that retained original. -/
theorem ballotJointReplayRetained_failure_le (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat) (δ : ENNReal)
    (accepted : A → Prop)
    (hs : ∀ path : PFunctor.FreeM.Path (ballotReplaySourceRun oa),
      accepted (PFunctor.FreeM.output _ path).1 → ∀ i,
      (ballotForkSelector n (PFunctor.FreeM.output _
        (ballotReplaySourcePath oa (select i) path))).isSome) :
    Pr[fun out => accepted out.1.1 ∧ out.2 = none | ballotJointReplayRetained oa select n k] ≤
      3*(n+1 : ENNReal)*δ + (1-(δ-(Fintype.card F : ENNReal)⁻¹)^3)^k := by
  classical
  unfold ballotJointReplayRetained
  refine le_trans (probEvent_bind_le_probEvent_add
    (p := ballotJointReplayBadContext oa select n δ)
    (ε := (1-(δ-(Fintype.card F : ENNReal)⁻¹)^3)^k) ?_) ?_
  · intro path _ hg
    rw [bind_pure_comp,probEvent_map]
    dsimp only [Function.comp_def]
    by_cases ha : accepted (PFunctor.FreeM.output _ path).1
    · simp only [ha,true_and,probEvent_eq_eq_probOutput]
      exact ballotJointReplayRepeatAtPath_failure_le oa select n k δ path (hs path ha) hg
    · simp only [ha,false_and,probEvent_False]
      exact zero_le
  · exact add_le_add (ballotJointReplay_bad_context_le oa select n δ) le_rfl

/-- Any observation of the returned original output and live cache has exactly
the original probability, including when extraction returns no witness. -/
theorem ballotJointReplayRetained_original_event (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat)
    (event : A × BallotOracleCache F G → Prop) :
    Pr[fun out => event out.1 | ballotJointReplayRetained oa select n k] =
      Pr[event | runBallotOracle oa ∅] := by
  classical
  let project := fun raw : A × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F =>
    (raw.1,ballotForkCacheProject raw.2.1)
  have hfirst : Pr[fun out => event out.1 | ballotJointReplayRetained oa select n k] =
      Pr[fun path => event (project (PFunctor.FreeM.output _ path)) |
        replayFirstPath (ballotReplaySourceRun oa)] := by
    unfold ballotJointReplayRetained
    rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
    apply tsum_congr
    intro path
    rw [bind_pure_comp,probEvent_map]
    dsimp only [Function.comp_def]
    by_cases hp : event (project (PFunctor.FreeM.output _ path))
    · simp only [project] at hp
      simp [hp,probFailure_of_liftM_PMF,project]
    · simp only [project] at hp
      simp [hp,project]
  have hsource : Pr[fun raw => event (project raw) | ballotReplaySourceRun oa] =
      Pr[event | runBallotOracle oa ∅] := by
    calc
      _ = Pr[fun raw => event (project raw) |
          simulateQ ballotForkEntropyImpl (ballotReplaySourceRun oa)] :=
        (probEvent_congr' (fun _ _ => Iff.rfl) (ballotFork_entropy_eval _)).symm
      _ = _ := by
        have h := congrArg (fun m => Pr[event | m]) (ballotFork_runtime_eq oa (∅,[]))
        have he : ballotForkCacheProject (∅ : (Unit × BallotForkPoint G →ₒ F).QueryCache) =
            (∅ : BallotOracleCache F G) := by funext key; rfl
        simpa only [he,probEvent_map,Function.comp_def,Prod.map,id_eq,ballotReplaySourceRun,project] using h
  calc
    _ = _ := hfirst
    _ = Pr[fun raw => event (project raw) | ballotReplaySourceRun oa] := by
      have h := congrArg (fun m => Pr[fun raw => event (project raw) | m])
        (map_output_replayFirstPath (ballotReplaySourceRun oa))
      simpa only [probEvent_map,Function.comp_def] using h
    _ = _ := hsource

/-- Exact original joint distribution, rather than conditioning it on extraction
success. The live cache is part of the equality. -/
theorem ballotJointReplayRetained_original (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n k : Nat) :
    evalSPMF (Prod.fst <$> ballotJointReplayRetained oa select n k) =
      evalSPMF (runBallotOracle oa ∅) := by
  apply evalSPMF_ext
  intro out
  have h := ballotJointReplayRetained_original_event oa select n k (fun x => x = out)
  rw [← probEvent_eq_eq_probOutput,probEvent_map]
  simpa only [Function.comp_def,probEvent_eq_eq_probOutput] using h

end Finite

#print axioms ballotJointReplayRetained_total_query_bound
#print axioms ballotJointReplayRetained_valid
#print axioms ballotJointReplayRetained_failure_le
#print axioms ballotJointReplayRetained_original_event
#print axioms ballotJointReplayRetained_original
#print axioms replayRepeat_supported
#print axioms replayRepeat_bound
#print axioms replayRepeat_failure
#print axioms ballotJointReplayRepeatAtPath_lossless
#print axioms ballotJointReplayRepeatAtPath_failure_le
end ExplainableCrypto.Helios.Computational
