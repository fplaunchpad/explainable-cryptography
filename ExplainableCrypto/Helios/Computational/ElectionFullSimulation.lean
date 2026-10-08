import ExplainableCrypto.Helios.Computational.ElectionPrefixSimulation
import ExplainableCrypto.Helios.Computational.ElectionTrusteeSimulation

/-! Composition of the actual prefix and finish proof simulations through the
original preparation, casting and guessing callbacks. This statistical hybrid
still uses the sampled secret for correct shares; it is not a DDH reduction. -/
namespace ExplainableCrypto.Helios.Computational.ElectionFullSimulation
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionCacheBudget
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev Output (F G : Type) := ((PublicResult F G × Bool) × Bool) × Cache F G

/-- The unmodified attacker actions and actual scheduled finish. -/
noncomputable def continuation {State : Type} (secret : F) (adversary : Adversary F G State)
    (before : PublicPrefix F G) : Comp F G (PublicResult F G × Bool) := do
  let (submission,saved) ← adversary.castBallot before
  let view ← ElectionNonceSchedule.finish secret before submission
  let guess ← adversary.guessVote saved view
  pure (view,guess)

noncomputable def afterReal {State : Type} (secret : F) (adversary : Adversary F G State)
    (before : (PublicPrefix F G × Bool) × Cache F G) : ProbComp (Output F G) :=
  (fun out => ((out.1,before.1.2),out.2)) <$> run (continuation secret adversary before.1.1) before.2

/-- All original public fields reach the original callbacks; the two private
collision flags are combined without changing either callback's interface. -/
def afterSim {State : Type} (secret : F) (adversary : Adversary F G State)
    (before : (PublicPrefix F G × Bool) × Cache F G) : ProbComp (Output F G) := do
  let cast ← run (adversary.castBallot before.1.1) before.2
  let finished ← (ElectionTrusteeSimulation.finishSim before.1.1 cast.1.1 (partialDecrypt secret)).run cast.2
  let guessed ← run (adversary.guessVote cast.1.2 finished.1.1) finished.2
  pure (((finished.1.1,guessed.1),before.1.2 || finished.1.2),guessed.2)

private theorem after_distance_le {State : Type} (secret : F) (adversary : Adversary F G State)
    (before : (PublicPrefix F G × Bool) × Cache F G) (k c : Nat)
    (hc : Covered before.2 k)
    (hcast : (adversary.castBallot before.1.1).IsQueryBoundP (isHash (F := F)) c)
    (hpk : before.1.1.parameters.publicKey = secret • before.1.1.parameters.generator)
    (hg : Function.Injective (fun r : F => r • before.1.1.parameters.generator)) :
    tvDist (afterReal secret adversary before) (afterSim secret adversary before) ≤
      (2*((k : ℝ)+c)+9) * (Fintype.card F : ℝ)⁻¹ := by
  simp only [afterReal,continuation,run_bind,run_pure,map_bind,map_pure,afterSim]
  apply tvDist_bind_left_le_const
  intro cast hcast'
  have hcache := run_covered _ c k hcast before.2 hc cast hcast'
  have h := (tvDist_bind_right_le (ElectionTrusteeSimulation.observe (adversary.guessVote cast.1.2)) _ _).trans
    (ElectionTrusteeSimulation.finish_distance_le secret before.1.1 cast.1.1 hpk hg cast.2 (k+c) hcache)
  have hm := (tvDist_map_le (fun out : Output F G => ((out.1.1,before.1.2 || out.1.2),out.2)) _ _).trans h
  simpa only [ElectionTrusteeSimulation.observe,map_eq_bind_pure_comp,Function.comp_def,
    bind_assoc,pure_bind,Bool.or_false,Nat.cast_add] using hm

/-- The whole proof-simulation hybrid. Correct shares still use the sampled
secret, so this definition makes no claim of DDH-challenge implementability. -/
noncomputable def worldSim {State : Type} (fingerprint : PublicParameters F G → Nat) (g : G)
    (adversary : Adversary F G State) (vote : Bool) (cache : Cache F G) : ProbComp (Output F G) := do
  let secret ← sampleNonzero F
  let before ← ElectionPrefixSimulation.sim fingerprint g (secret • g) vote cache
  afterSim secret adversary before

private theorem fixed_distance_le {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (hg : Function.Injective (fun r : F => r • g))
    (adversary : Adversary F G State) (vote : Bool) (cache : Cache F G) (k c : Nat)
    (hc : Covered cache k)
    (hcast : ∀ before, (adversary.castBallot before).IsQueryBoundP (isHash (F := F)) c) :
    tvDist ((fun out => ((out.1,false),out.2)) <$> run
      (ElectionPrefixSimulation.source fingerprint g secret vote >>= continuation secret adversary) cache)
      (ElectionPrefixSimulation.sim fingerprint g (secret • g) vote cache >>= afterSim secret adversary) ≤
        (11*(k : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by
  have hfirst := (tvDist_bind_right_le (afterReal secret adversary) _ _).trans
    (ElectionPrefixSimulation.prefix_distance_le fingerprint g secret hg vote cache k hc)
  have hsecond : tvDist
      (ElectionPrefixSimulation.sim fingerprint g (secret • g) vote cache >>= afterReal secret adversary)
      (ElectionPrefixSimulation.sim fingerprint g (secret • g) vote cache >>= afterSim secret adversary) ≤
        (2*(((2*k+13 : Nat) : ℝ)+c)+9) * (Fintype.card F : ℝ)⁻¹ := by
    apply tvDist_bind_left_le_const
    intro before hbefore
    have hcov := ElectionPrefixSimulation.sim_covered fingerprint g (secret • g) vote cache k hc before hbefore
    have hparams := ElectionPrefixSimulation.sim_parameters fingerprint g (secret • g) vote cache before hbefore
    exact after_distance_le secret adversary before (2*k+13) c hcov (hcast _)
      (by rw [hparams.1,hparams.2]) (by simpa only [hparams.1] using hg)
  have hsum : (7*(k : ℝ)+91) / (Fintype.card F : ℝ) +
      (2*(((2*k+13 : Nat) : ℝ)+c)+9) * (Fintype.card F : ℝ)⁻¹ =
      (11*(k : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have h := (tvDist_triangle _ _ _).trans ((add_le_add hfirst hsecond).trans_eq hsum)
  simpa only [afterReal,run_bind,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind] using h

/-- The original complete world is statistically close to the composed hybrid,
including all rejection fields, attacker guesses, private flag and final cache. -/
theorem world_distance_le {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (adversary : Adversary F G State) (vote : Bool) (cache : Cache F G) (k c : Nat)
    (hc : Covered cache k)
    (hcast : ∀ before, (adversary.castBallot before).IsQueryBoundP (isHash (F := F)) c) :
    tvDist ((fun out => ((out.1,false),out.2)) <$>
      run (ElectionExtraction.worldSource fingerprint g adversary vote) cache)
      (worldSim fingerprint g adversary vote cache) ≤
        (11*(k : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by
  have heq := evalSPMF_map_eq_of_evalSPMF_eq
    (ElectionNonceSchedule.world_eq fingerprint g adversary vote cache)
    (fun out => ((out.1,false),out.2))
  have h : tvDist ((fun out => ((out.1,false),out.2)) <$>
      run (ElectionNonceSchedule.world fingerprint g adversary vote) cache)
      (worldSim fingerprint g adversary vote cache) ≤
        (11*(k : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by
    rw [ElectionPrefixSimulation.world_source]
    simp only [worldSim,run_liftProb_bind,map_bind]
    apply tvDist_bind_left_le_const
    intro secret _
    exact fixed_distance_le fingerprint g secret hg adversary vote cache k c hc hcast
  unfold tvDist at h ⊢
  rw [heq]
  exact h

/-- The same preparation and fair challenge bit as the actual game. -/
noncomputable def preparedSim {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) : ProbComp (Output F G) := do
  let initial ← run prepare ∅
  let vote ← uniformSample Bool
  let out ← worldSim fingerprint g (adversary initial.1) vote initial.2
  pure (((out.1.1.1,decide (out.1.1.2 = vote)),out.1.2),out.2)

/-- Full prepared-source bound with the initial cache and parameter relations
 derived from actual executions. Guessing may make arbitrary later queries.
 This closes proof-simulation composition, not computational ballot secrecy. -/
theorem prepared_distance_le {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G State) (p c : Nat)
    (hprepare : prepare.IsQueryBoundP (isHash (F := F)) p)
    (hcast : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP (isHash (F := F)) c) :
    tvDist ((fun out => ((out.1,false),out.2)) <$>
      run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅)
      (preparedSim fingerprint g prepare adversary) ≤
        (11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by
  simp only [ElectionExtraction.preparedSource,preparedSim,run_bind,run_pure,run_liftProb,
    bind_map_left,map_bind,map_pure]
  apply tvDist_bind_left_le_const
  intro initial hi
  have hc : Covered initial.2 p := by
    simpa using run_covered prepare p 0 hprepare ∅ Covered.empty initial hi
  apply tvDist_bind_left_le_const
  intro vote _
  have h := (tvDist_map_le
    (fun out : Output F G => (((out.1.1.1,decide (out.1.1.2 = vote)),out.1.2),out.2)) _ _).trans
    (world_distance_le fingerprint g hg (adversary initial.1) vote initial.2 p c hc (hcast initial.1))
  simpa only [map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind] using h

#print axioms world_distance_le
#print axioms prepared_distance_le
end ExplainableCrypto.Helios.Computational.ElectionFullSimulation
