import ExplainableCrypto.Helios.Computational.ElectionDDHPrefixRepeat

/-! Compare the actual historical prepared source with a real-DDH challenge
source. Secret-based finishing is a comparison hybrid, not the DDH reduction. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionProgrammedSource (State Source Inv raw trustee evaluate evaluate_bind evaluate_pure)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem lower_prob {B : Type} (oa : ProbComp B) (cache : Cache F G) :
    (ElectionReplaySource.lower (liftProb oa)).run cache =
      (fun x => (x,cache)) <$> liftComp oa (BallotOracleSpec F G) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp [ElectionReplaySource.lower,liftProb]
  | query_bind t next ih =>
    simp only [liftProb,liftComp_bind,ElectionReplaySource.lower,simulateQ_bind,StateT.run_bind]
    change (do
      let out ← (do let x ← liftComp (liftM (unifSpec.query t) : ProbComp _) (BallotOracleSpec F G)
                    pure (x,cache))
      (ElectionReplaySource.lower (liftProb (next out.1))).run out.2) = _
    simp only [bind_assoc,pure_bind,ih,map_bind]

omit [Fintype F] [DecidableEq F] in
/-- Pure random draws preserve the entire source state and the actual live cache.
This exact runtime lemma justifies moving independent coins in interpreted laws. -/
theorem raw_prob {B : Type} (g pk : G) (oa : ProbComp B) (s : State F G)
    (live : BallotOracleCache F G) :
    evaluate (raw g pk (liftProb oa)) s live = (fun x => ((x,s),live)) <$> oa := by
  unfold raw evaluate
  dsimp only [StateT.run]
  have hlower := lower_prob (F := F) (G := G) oa s.cache
  dsimp only [StateT.run] at hlower
  rw [hlower]
  simp only [liftComp_map,simulateQ_map]
  change runBallotOracle (do
    let out ← ((fun x => (x,s.cache)) <$> simulateQ (ballotProgrammedImpl g pk)
      (liftComp (liftComp oa (BallotOracleSpec F G)) (BallotProofOracleSpec F G))).run s.ballot
    pure (out.1.1,ElectionProgrammedSource.rebuild out.1.2 out.2)) live = _
  rw [StateT.run_map]
  simp only [bind_map_left]
  have hl : liftComp (liftComp oa (BallotOracleSpec F G)) (BallotProofOracleSpec F G) =
      liftComp oa (BallotProofOracleSpec F G) := by
    clear hlower
    induction oa using OracleComp.inductionOn with
    | pure x => rfl
    | query_bind t next ih =>
      simp only [liftComp_bind,ih]
      rfl
  rw [hl,runBallotOracle_bind,run_programmed_prob]
  simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp,Functor.map_map]
  congr 1
  funext x
  cases s
  simp only [ElectionProgrammedSource.rebuild,State.ballot,replace_project]


/-- The actual post-submission computation, including rejection publication and
saved-state-dependent guessing. This comparison continuation uses the secret. -/
def finishAfterCast {Saved : Type} (g pk : G) (secret : F)
    (adversary : Adversary F G Saved) (vote : Bool) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (saved : Saved)
    (cast : Decision × List (BoardEntry F G)) : Source F G (PublicResult F G × Bool) := do
  let cts := boardTally cast.2
  let shares := fun j => partialDecrypt secret (cts j)
  let proofs ← trustee (ElectionTrusteeSimulation.simPair g pk cts shares)
  let view := ElectionTrusteeSimulation.publication before submission cast shares proofs
  let guess ← raw g pk (adversary.guessVote saved view)
  pure (view,decide (guess = vote))

private def afterHonest {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) (key : SchnorrProof F G) (honest : Cast F G) :
    Source F G (PublicResult F G × Bool) := do
  let before := ElectionPrefixSimulation.publication fingerprint g (secret • g) key honest
  let made ← raw g (secret • g) ((adversary initial).castBallot before)
  let cast ← raw g (secret • g) (liftBallot (repairedSubmitOracle g (secret • g) 2 before.board made.1))
  finishAfterCast g (secret • g) secret (adversary initial) vote before made.1 made.2 cast

/-- The real-challenge comparison finishes the exact public-input prefix. The
secret is an explicit hybrid input; the executable reduction must replace it. -/
def completedReal {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (secret : F) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) : Source F G (PublicResult F G × Bool) := do
  let out ← preparedPrefix fingerprint g pk A T prepare adversary
  finishAfterCast g pk secret (adversary out.initial) out.vote out.before out.submission out.saved out.cast

private abbrev RunOutput (F G : Type) :=
  ((PublicResult F G × Bool) × State F G) × BallotOracleCache F G

private def replacedHonest {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) (key : SchnorrProof F G)
    (s : State F G) (live : BallotOracleCache F G) : ProbComp (RunOutput F G) := do
  let x ← uniformSample F
  let a ← uniformSample F
  let t ← uniformSample F
  let b ← uniformSample F
  let honest ← evaluate (ballots g (secret • g) (x • g) (x • (secret • g)) t a b vote) s live
  evaluate (afterHonest fingerprint g secret adversary initial vote key honest.1.1.1) honest.1.2 honest.2

/-- The honest-nonce replacement survives the actual casting, rejection, trustee
publication and guessing continuation, retaining both final state and live cache. -/
theorem after_honest_real_distance_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) (key : SchnorrProof F G)
    (s : State F G) (live : BallotOracleCache F G) :
    tvDist (evaluate (do
      let honest ← ElectionProgrammedSource.ballots g (secret • g) vote
      afterHonest fingerprint g secret adversary initial vote key honest) s live)
      (replacedHonest fingerprint g secret adversary initial vote key s live) ≤
      4 * (Fintype.card F : ℝ)⁻¹ := by
  have h := (tvDist_bind_right_le (fun out : (Cast F G × State F G) × BallotOracleCache F G =>
    evaluate (afterHonest fingerprint g secret adversary initial vote key out.1.1) out.1.2 out.2) _ _).trans
      (ballots_real_distance_le g (secret • g) vote s live)
  simpa only [evaluate_bind,bind_map_left,map_bind,bind_assoc,replacedHonest] using h

private def replacedWorld {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) (s : State F G) (live : BallotOracleCache F G) :
    ProbComp (RunOutput F G) := do
  let key ← evaluate (trustee (TrusteeReachableSimulation.keySim g (secret • g))) s live
  replacedHonest fingerprint g secret adversary initial vote key.1.1 key.1.2 key.2

private def localReal {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (s : State F G) (live : BallotOracleCache F G) : ProbComp (RunOutput F G) := do
  let initial ← evaluate (raw g 0 prepare) s live
  let vote ← uniformSample Bool
  let secret ← uniformSample F
  replacedWorld fingerprint g secret adversary initial.1.1 vote initial.1.2 initial.2

/-- One key draw and four honest nonces account for the complete 5/q loss.
Every actual continuation and rejection branch remains in both distributions. -/
private theorem local_real_distance_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (s : State F G) (live : BallotOracleCache F G) :
    tvDist (evaluate (ElectionProgrammedSource.prepared fingerprint g prepare adversary) s live)
      (localReal fingerprint g prepare adversary s live) ≤ 5 * (Fintype.card F : ℝ)⁻¹ := by
  simp only [ElectionProgrammedSource.prepared,evaluate_bind,raw_prob,bind_map_left,localReal]
  apply tvDist_bind_left_le_const
  intro initial _
  apply tvDist_bind_left_le_const
  intro vote _
  let target := fun secret => replacedWorld fingerprint g secret adversary initial.1.1 vote initial.1.2 initial.2
  have hnonce : tvDist
      (sampleNonzero F >>= fun secret => evaluate (do
        let key ← trustee (TrusteeReachableSimulation.keySim g (secret • g))
        let honest ← ElectionProgrammedSource.ballots g (secret • g) vote
        afterHonest fingerprint g secret adversary initial.1.1 vote key honest) initial.1.2 initial.2)
      (sampleNonzero F >>= target) ≤ 4 * (Fintype.card F : ℝ)⁻¹ := by
    apply tvDist_bind_left_le_const
    intro secret _
    simp only [evaluate_bind,target,replacedWorld]
    apply tvDist_bind_left_le_const
    intro key _
    simpa only [evaluate_bind] using
      after_honest_real_distance_le fingerprint g secret adversary initial.1.1 vote key.1.1 key.1.2 key.2
  have hkey := (tvDist_bind_right_le target _ _).trans (sampleNonzero_uniform_tv_le (F := F))
  have h := (tvDist_triangle _ _ _).trans (add_le_add hnonce hkey)
  have harith : 4 * (Fintype.card F : ℝ)⁻¹ + (Fintype.card F : ℝ)⁻¹ =
      5 * (Fintype.card F : ℝ)⁻¹ := by ring
  rw [harith] at h
  simpa only [target,afterHonest,finishAfterCast,evaluate_bind,evaluate_pure] using h


/-- Real-DDH input distribution with actual public-input prefix and full
secret-based comparison finish. Key/exponent coins are outside the prefix. -/
noncomputable def realGame {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    ProbComp (((PublicResult F G × Bool) × State F G) × BallotOracleCache F G) := do
  let secret ← uniformSample F
  let x ← uniformSample F
  evaluate (completedReal fingerprint g (secret • g) (x • g) (x • (secret • g))
    secret prepare adversary) .empty ∅

omit [Fintype F] in
/-- Moving independent key/exponent coins identifies interpreted distributions
only. All replay positions are those of the already checked actual prefix. -/
private theorem local_real_eq {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    evalSPMF (localReal fingerprint g prepare adversary .empty ∅) =
      evalSPMF (realGame fingerprint g prepare adversary) := by
  simp only [localReal,replacedWorld,replacedHonest,realGame,completedReal,preparedPrefix,
    drawKnown,evaluate_bind,raw_prob,bind_map_left,bind_assoc,pure_bind,afterHonest]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext initial
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro secret
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext initial
    rw [evalSPMF_bind]; arg 2; ext vote
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext initial
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro x
  apply evalSPMF_bind_congr'
  intro initial
  apply evalSPMF_bind_congr'
  intro vote
  apply evalSPMF_bind_congr'
  intro key
  conv_lhs => rw [evalSPMF_bind_bind_swap]

/-- Complete real-challenge replacement inside the actual source. The 5/q bound
includes the historical nonzero key and all four honest nonces. -/
theorem source_real_distance_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    tvDist (evaluate (ElectionProgrammedSource.prepared fingerprint g prepare adversary) .empty ∅)
      (realGame fingerprint g prepare adversary) ≤ 5 * (Fintype.card F : ℝ)⁻¹ := by
  have h := local_real_distance_le fingerprint g prepare adversary .empty ∅
  unfold tvDist at h ⊢
  rwa [local_real_eq] at h

/-- The original complete historical game is close to the real-DDH comparison
source, including every public field, winning bit, private flag and final cache.
The comparison finish uses the sampled secret; public-input finishing is
proved separately in `ElectionDDHExtractedFinish`. -/
theorem prepared_real_distance_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (p c : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c) :
    tvDist ((fun out => ((out.1,false),out.2)) <$>
      run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅)
      (ElectionProgrammedSource.result <$> realGame fingerprint g prepare adversary) ≤
      (11*(p : ℝ)+2*c+131) / (Fintype.card F : ℝ) := by
  have hnonce := (tvDist_map_le ElectionProgrammedSource.result _ _).trans
    (source_real_distance_le fingerprint g prepare adversary)
  rw [ElectionProgrammedSource.prepared_runtime_eq] at hnonce
  have hsim := ElectionFullSimulation.prepared_distance_le fingerprint g hg prepare adversary p c hp hc
  have h := (tvDist_triangle _ _ _).trans (add_le_add hsim hnonce)
  have harith : (11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ) + 5*(Fintype.card F : ℝ)⁻¹ =
      (11*(p : ℝ)+2*c+131) / (Fintype.card F : ℝ) := by
    simp only [div_eq_mul_inv]
    ring
  rwa [harith] at h


omit [Fintype F] [DecidableEq F] in
/-- The actual finishing continuation publishes the supplied retained decision
and board on every branch, even after arbitrary later guessing queries. -/
theorem finishAfterCast_publication {Saved : Type} (g pk : G) (secret : F)
    (adversary : Adversary F G Saved) (vote : Bool) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (saved : Saved) (cast : Decision × List (BoardEntry F G))
    (s : State F G) (live : BallotOracleCache F G)
    (out : ((PublicResult F G × Bool) × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (finishAfterCast g pk secret adversary vote before submission saved cast) s live)) :
    out.1.1.1.beforeTally = before ∧ out.1.1.1.submission = submission ∧
      out.1.1.1.decision = cast.1 ∧ out.1.1.1.board = cast.2 ∧
      out.1.1.1.encryptedTally = boardTally cast.2 ∧
      out.1.1.1.decryptionShares = (fun j => partialDecrypt secret (boardTally cast.2 j)) := by
  simp only [finishAfterCast,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨proofs,_,guess,_,rfl⟩ := ho
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms finishAfterCast_publication
#print axioms source_real_distance_le
#print axioms prepared_real_distance_le
#print axioms after_honest_real_distance_le
#print axioms raw_prob
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
