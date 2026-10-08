import ExplainableCrypto.Helios.Computational.StrongBallotSimulator
import ExplainableCrypto.Helios.Computational.NonzeroSimulationBridge

/-! Comparison of one actual historical oracle proof with the stateful simulator.
The full proof, internal collision flag and final cache are compared. Full-field
coins are a proof intermediate only, not a change to the historical algorithm. -/
namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleSpec
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

noncomputable def strongBallotRealOracle (stmt : BallotStatement G) (wit : BallotWitness F) :
    StateT (BallotOracleCache F G) ProbComp (Proof01 F G × Bool) := fun cache =>
  (fun out => ((out.1,false),out.2)) <$> runBallotOracle (strongBallotProofOracle stmt wit) cache

private def fullCoins : ProbComp (BallotPrivateCoins F) := do
  let w ← uniformSample F
  let e ← uniformSample F
  let z ← uniformSample F
  pure (w,e,z)

private def realContinuation (stmt : BallotStatement G) (wit : BallotWitness F)
    (cache : BallotOracleCache F G) (coins : BallotPrivateCoins F) :=
  (fun out => ((out.1,false),out.2)) <$>
    runBallotOracle (strongBallotProofWithCoinsOracle stmt wit coins) cache

private def simFinish (stmt : BallotStatement G) (cache : BallotOracleCache F G)
    (t : BallotCommitment G × F × BallotResponse F) :
    (Proof01 F G × Bool) × BallotOracleCache F G :=
  let p := ballotTranscriptProof t.1 t.2.1 t.2.2
  match cache (stmt,t.1) with
  | some _ => ((p,true),cache)
  | none => ((p,false),cache.cacheQuery (stmt,t.1) t.2.1)

private def simContinuation (stmt : BallotStatement G) (wit : BallotWitness F)
    (cache : BallotOracleCache F G) (coins : BallotPrivateCoins F) := do
  let c ← uniformSample F
  pure (simFinish stmt cache (ballotCommitWith stmt wit coins,c,ballotRespondWith wit coins c))

omit [DecidableEq F] in
private theorem actual_eq_nonzero (stmt : BallotStatement G) (wit : BallotWitness F)
    (cache : BallotOracleCache F G) :
    (strongBallotRealOracle stmt wit).run cache =
      (do
        let w ← sampleNonzero F
        let e ← sampleNonzero F
        let z ← sampleNonzero F
        realContinuation stmt wit cache (w,e,z)) := by
  simp only [strongBallotRealOracle, StateT.run, strongBallotProofOracle,
    runBallotOracle_lift_bind, map_bind, realContinuation]

omit [Fintype F] [DecidableEq F] in
private theorem continuations_eq_off_cache (stmt : BallotStatement G) (wit : BallotWitness F)
    (cache : BallotOracleCache F G) (coins : BallotPrivateCoins F)
    (hfresh : ¬ (cache (stmt,ballotCommitWith stmt wit coins)).isSome = true) :
    𝒮[realContinuation stmt wit cache coins] = 𝒮[simContinuation stmt wit cache coins] := by
  have hc : cache (stmt,ballotCommitWith stmt wit coins) = none := by
    cases h : cache (stmt,ballotCommitWith stmt wit coins) <;> simp_all
  apply congrArg evalSPMF
  simp only [realContinuation, runBallotOracle, strongBallotProofWithCoinsOracle,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  change (do
    let answer ← runBallotOracle (ballotChallengeOracle stmt (ballotCommitWith stmt wit coins)) cache
    pure ((ballotTranscriptProof (ballotCommitWith stmt wit coins) answer.1
      (ballotRespondWith wit coins answer.1),false),answer.2)) = _
  rw [runBallotOracle_query, hc]
  simp [simContinuation, simFinish, hc, monad_norm]

omit [Fintype F] in
private theorem full_reference_maps_to_simulator (stmt : BallotStatement G) (wit : BallotWitness F)
    (hw : stmt.Witnesses wit) (cache : BallotOracleCache F G) :
    𝒮[fullCoins (F := F) >>= simContinuation stmt wit cache] =
      𝒮[(strongBallotSimOracle (F := F) stmt).run cache] := by
  have he := ballotSigma_full_hvzk (F := F) (G := G) stmt wit (by simpa using hw)
  have hm := evalSPMF_map_eq_of_evalSPMF_eq he (simFinish stmt cache)
  have hr : fullCoins (F := F) >>= simContinuation stmt wit cache =
      simFinish stmt cache <$> ((ballotSigmaWithSampler (G := G) (uniformSample F)).realTranscript stmt wit) := by
    simp only [ChallengeVerifyProtocol.realTranscript, ballotSigmaWithSampler, fullCoins,
      simContinuation, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  have hs : (strongBallotSimOracle (F := F) stmt).run cache =
      simFinish stmt cache <$> ballotFullSimTranscript (F := F) stmt := by
    unfold strongBallotSimOracle StateT.run
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro t
    simp only [Function.comp_def, simFinish]
    cases cache (stmt,t.1) <;> rfl
  rw [hr, hs]
  exact hm

omit [Fintype F] in
private theorem full_reference_bad_probability (stmt : BallotStatement G) (wit : BallotWitness F)
    (hw : stmt.Witnesses wit) (cache : BallotOracleCache F G) :
    Pr[fun coins => (cache (stmt,ballotCommitWith stmt wit coins)).isSome = true | fullCoins (F := F)] =
      Pr[fun t => (cache (stmt,t.1)).isSome = true | ballotFullSimTranscript (F := F) stmt] := by
  have he := ballotSigma_full_hvzk (F := F) (G := G) stmt wit (by simpa using hw)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) he.symm]
  have hr : (ballotSigmaWithSampler (G := G) (uniformSample F)).realTranscript stmt wit =
      (do
        let coins ← fullCoins (F := F)
        let c ← uniformSample F
        pure (ballotCommitWith stmt wit coins,c,ballotRespondWith wit coins c)) := by
    simp [ChallengeVerifyProtocol.realTranscript, ballotSigmaWithSampler, fullCoins, monad_norm]
  rw [hr]
  rw [probEvent_eq_tsum_ite, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro coins
  rw [probEvent_bind_of_const (uniformSample F)
    (r := if (cache (stmt,ballotCommitWith stmt wit coins)).isSome = true then 1 else 0)
    (by intro c _; simp)]
  simp

/-- State-inclusive one-step programming distance. The collision cover is explicit;
query bounds for a reachable adaptive election must still be derived. -/
theorem strongBallot_programming_step_distance_le (stmt : BallotStatement G) (wit : BallotWitness F)
    (hw : stmt.Witnesses wit) (hg : Function.Injective (fun r : F => r • stmt.generator))
    (cache : BallotOracleCache F G) (queries : Finset (BallotStatement G × BallotCommitment G))
    (hcover : ∀ key, (cache key).isSome = true → key ∈ queries) :
    tvDist ((strongBallotRealOracle stmt wit).run cache) ((strongBallotSimOracle (F := F) stmt).run cache) ≤
      3 * (Fintype.card F : ℝ)⁻¹ + (queries.card : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
  have hn : tvDist ((strongBallotRealOracle stmt wit).run cache)
      (fullCoins (F := F) >>= realContinuation stmt wit cache) ≤ 3 * (Fintype.card F : ℝ)⁻¹ := by
    rw [actual_eq_nonzero]
    simpa only [fullCoins, monad_norm] using
      three_nonzero_draws_tv_le (fun w e z => realContinuation stmt wit cache (w,e,z))
  have hb := tvDist_bind_left_event_le (fullCoins (F := F))
    (realContinuation stmt wit cache) (simContinuation stmt wit cache)
    (fun coins => (cache (stmt,ballotCommitWith stmt wit coins)).isSome = true)
    (continuations_eq_off_cache stmt wit cache)
  rw [full_reference_bad_probability stmt wit hw cache] at hb
  have hp := strongBallotSimOracle_bad_probability_le stmt hg cache queries hcover
  rw [strongBallotSimOracle_bad_probability] at hp
  have hq : (Fintype.card F : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  have hfinite : (queries.card : ENNReal) * (Fintype.card F : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hq)
  have hpr := ENNReal.toReal_mono hfinite hp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast] at hpr
  have hs : tvDist (fullCoins (F := F) >>= realContinuation stmt wit cache)
      ((strongBallotSimOracle (F := F) stmt).run cache) ≤
        (queries.card : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
    have he := full_reference_maps_to_simulator stmt wit hw cache
    unfold tvDist at hb ⊢
    rw [he] at hb
    exact hb.trans hpr
  exact (tvDist_triangle _ _ _).trans (add_le_add hn hs)

#print axioms strongBallot_programming_step_distance_le

end ExplainableCrypto.Helios.Computational
