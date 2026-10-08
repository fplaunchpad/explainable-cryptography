import ExplainableCrypto.Helios.Computational.ElectionFullSimulation
import ExplainableCrypto.Helios.Computational.RepairedSubmissionOracle

/-! Replayable use of the existing programmed-ballot adapter in the full
proof-simulation hybrid. Auxiliary proof domains keep their original cache. -/
namespace ExplainableCrypto.Helios.Computational.ElectionProgrammedSource
open OracleComp OracleSpec ElectionOracle ElectionCache
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

structure State (F G : Type) where
  cache : Cache F G
  bad : Bool
  programmed : List (BallotStatement G)

def State.ballot (s : State F G) : BallotProgrammedState F G :=
  ⟨project s.cache,s.bad,s.programmed⟩

def State.empty : State F G := ⟨∅,false,[]⟩

def rebuild (aux : Cache F G) (s : BallotProgrammedState F G) : State F G :=
  ⟨replace aux s.cache,s.bad,s.programmed⟩

def Inv (s : State F G) (live : BallotOracleCache F G) := BallotProgrammedInv s.ballot live

abbrev Source (F G : Type) := StateT (State F G) (BallotOracleComp F G)

def evaluate {A : Type} (oa : Source F G A) (s : State F G) (live : BallotOracleCache F G) :=
  runBallotOracle (oa.run s) live

def result {A : Type} (out : (A × State F G) × BallotOracleCache F G) : (A × Bool) × Cache F G :=
  ((out.1.1,out.1.2.bad),out.1.2.cache)

/-- Raw full-election computation, including auxiliary proof queries, passes
through the existing live/shadow ballot handler. -/
def raw {A : Type} (g pk : G) (oa : Comp F G A) : Source F G A := fun s => do
  let out ← (simulateQ (ballotProgrammedImpl g pk)
    (liftComp ((ElectionReplaySource.lower oa).run s.cache) (BallotProofOracleSpec F G))).run s.ballot
  pure (out.1.1,rebuild out.1.2 out.2)

omit [Fintype F] [DecidableEq F] in
private theorem raw_evaluate {A : Type} (g pk : G) (oa : Comp F G A)
    (s : State F G) (live : BallotOracleCache F G) :
    evaluate (raw g pk oa) s live =
      (fun out => ((out.1.1.1,rebuild out.1.1.2 out.1.2),out.2)) <$>
        runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
          (liftComp ((ElectionReplaySource.lower oa).run s.cache) (BallotProofOracleSpec F G))).run s.ballot) live := by
  change runBallotOracle (_ >>= fun out : (A × Cache F G) × BallotProgrammedState F G => pure (out.1.1,rebuild out.1.2 out.2)) live = _
  rw [runBallotOracle_bind]
  simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp]

omit [Fintype F] [DecidableEq F] in
/-- Exact runtime of arbitrary raw callbacks, including full cache and flag. -/
theorem raw_runtime {A : Type} (g pk : G) (oa : Comp F G A) (s : State F G)
    (live : BallotOracleCache F G) (hi : Inv s live) :
    result <$> evaluate (raw g pk oa) s live =
      (fun out => ((out.1,s.bad),out.2)) <$> run oa s.cache := by
  have h := congrArg (fun m => (fun out =>
    ((out.1.1,out.2.2),replace out.1.2 out.2.1)) <$> m)
    (ballotProgrammed_runtime_eq_of_inv g pk
      (liftComp ((ElectionReplaySource.lower oa).run s.cache) (BallotProofOracleSpec F G)) s.ballot live hi)
  rw [runBallotProofSim_raw] at h
  have hl := congrArg (fun m => (fun out => ((out.1,s.bad),out.2)) <$> m)
    (ElectionReplaySource.lower_run oa s.cache (project s.cache))
  simp only [replace_project] at hl
  simp only [Functor.map_map,State.ballot,BallotProgrammedState.toSimState] at h
  simp only [Functor.map_map,ElectionReplaySource.restore] at hl
  rw [← hl]
  rw [raw_evaluate]
  simpa only [result,rebuild,State.ballot,Functor.map_map,Function.comp_def] using h

omit [Fintype F] [DecidableEq F] in
/-- Consistency is preserved after arbitrary preparation/casting/guessing code. -/
theorem raw_inv {A : Type} (g pk : G) (oa : Comp F G A) (s : State F G)
    (live : BallotOracleCache F G) (hi : Inv s live)
    (out : (A × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (raw g pk oa) s live)) : Inv out.1.2 out.2 := by
  rw [raw_evaluate,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  exact ballotProgrammed_preserves_inv_of_inv g pk _ s.ballot live hi mid hm

/-- The existing sampled honest-pair program runs in the same source and records
its actual programmed statements. -/
noncomputable def ballots (g pk : G) (vote : Bool) : Source F G (ElectionPrefixSimulation.Cast F G) :=
  fun s => do
    let out ← (simulateQ (ballotProgrammedImpl g pk) (repairedCastHonestPairOracle g pk vote)).run s.ballot
    pure (out.1,rebuild s.cache out.2)

private theorem ballots_evaluate (g pk : G) (vote : Bool)
    (s : State F G) (live : BallotOracleCache F G) :
    evaluate (ballots g pk vote) s live =
      (fun out => ((out.1.1,rebuild s.cache out.1.2),out.2)) <$>
        runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
          (repairedCastHonestPairOracle g pk vote)).run s.ballot) live := by
  change runBallotOracle (_ >>= fun out : ElectionPrefixSimulation.Cast F G × BallotProgrammedState F G => pure (out.1,rebuild s.cache out.2)) live = _
  rw [runBallotOracle_bind]
  simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp]

theorem ballots_runtime (g pk : G) (vote : Bool) (s : State F G)
    (live : BallotOracleCache F G) (hi : Inv s live) :
    result <$> evaluate (ballots g pk vote) s live =
      ElectionPrefixSimulation.ballotsSim g pk vote s.bad s.cache := by
  have h := congrArg (fun m => ElectionPrefixSimulation.restore s.cache <$> m)
    (ballotProgrammed_runtime_eq_of_inv g pk (repairedCastHonestPairOracle g pk vote) s.ballot live hi)
  rw [ballots_evaluate]
  simpa only [result,rebuild,Functor.map_map,Function.comp_def,ElectionPrefixSimulation.ballotsSim,
    ElectionPrefixSimulation.restore,BallotProgrammedState.toSimState,State.ballot] using h

theorem ballots_inv (g pk : G) (vote : Bool) (s : State F G)
    (live : BallotOracleCache F G) (hi : Inv s live)
    (out : (ElectionPrefixSimulation.Cast F G × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (ballots g pk vote) s live)) : Inv out.1.2 out.2 := by
  rw [ballots_evaluate,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  exact ballotProgrammed_preserves_inv_of_inv g pk _ s.ballot live hi mid hm


/-- Trustee proof simulation uses private coins and auxiliary proof domains.
Ballot challenges remain in the live source through `raw`. -/
def trustee {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool)) : Source F G A := fun s => do
  let out ← liftComp (step.run s.cache) (BallotOracleSpec F G)
  pure (out.1.1,⟨out.2,s.bad || out.1.2,s.programmed⟩)

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem trustee_evaluate {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool))
    (s : State F G) (live : BallotOracleCache F G) :
    evaluate (trustee step) s live =
      (fun out => ((out.1.1,(⟨out.2,s.bad || out.1.2,s.programmed⟩ : State F G)),live)) <$> step.run s.cache := by
  change runBallotOracle (liftComp (step.run s.cache) (BallotOracleSpec F G) >>= fun out =>
    pure (out.1.1,(⟨out.2,s.bad || out.1.2,s.programmed⟩ : State F G))) live = _
  rw [runBallotOracle_lift_bind]
  simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp]

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem trustee_inv {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool))
    (hp : ∀ cache out, out ∈ support (step.run cache) → project out.2 = project cache)
    (s : State F G) (live : BallotOracleCache F G) (hi : Inv s live)
    (out : (A × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (trustee step) s live)) : Inv out.1.2 out.2 := by
  rw [trustee_evaluate,support_map] at ho
  obtain ⟨z,hz,rfl⟩ := ho
  unfold Inv BallotProgrammedInv State.ballot at hi ⊢
  simpa only [hp s.cache z hz] using hi

omit [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem trustee_project {H : Type} [AddCommGroup H] [Module F H]
    (base key : H) (tag : H → Key G)
    (ht : ∀ x stmt commit, tag x ≠ Key.ballot stmt commit)
    (cache : Cache F G) (out : (SchnorrProof F H × Bool) × Cache F G)
    (ho : out ∈ support ((TrusteeOracleSimulation.sim base key tag).run cache)) :
    project out.2 = project cache := by
  simp only [TrusteeOracleSimulation.sim,StateT.run,support_map] at ho
  obtain ⟨t,_,rfl⟩ := ho
  unfold TrusteeOracleSimulation.finish
  cases cache (tag t.1)
  · funext x
    simp [project,QueryCache.cacheQuery,Ne.symm (ht t.1 x.1 x.2)]
  · rfl

omit [Fintype F] [DecidableEq F] in
private theorem key_project (g pk : G) (cache : Cache F G)
    (out : (SchnorrProof F G × Bool) × Cache F G)
    (ho : out ∈ support ((TrusteeReachableSimulation.keySim (F := F) g pk).run cache)) :
    project out.2 = project cache :=
  trustee_project g pk (Key.key g pk) (by intros; simp) cache out ho

omit [Fintype F] [DecidableEq F] in
/-- Actual public-key proof simulation preserves the ballot-cache invariant. -/
theorem key_inv (g pk : G) (s : State F G) (live : BallotOracleCache F G)
    (hi : Inv s live)
    (out : (SchnorrProof F G × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (trustee (TrusteeReachableSimulation.keySim g pk)) s live)) :
    Inv out.1.2 out.2 := trustee_inv _ (key_project g pk) s live hi out ho

omit [Fintype F] [DecidableEq F] in
private theorem pair_project (g pk : G) (cts : Fin 2 → Ciphertext G) (shares : Fin 2 → G)
    (cache : Cache F G) (out : ((Fin 2 → ElectionTrusteeSimulation.PartialProof F G) × Bool) × Cache F G)
    (ho : out ∈ support ((ElectionTrusteeSimulation.simPair g pk cts shares).run cache)) :
    project out.2 = project cache := by
  simp only [ElectionTrusteeSimulation.simPair,ElectionTrusteeSimulation.pair,StateT.run,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,rfl⟩ := ho
  have h0 := trustee_project (g,(cts 0).1) (pk,shares 0)
    (Key.decryption g pk (cts 0) (shares 0)) (by intros; simp) cache a ha
  have h1 := trustee_project (g,(cts 1).1) (pk,shares 1)
    (Key.decryption g pk (cts 1) (shares 1)) (by intros; simp) a.2 b hb
  exact h1.trans h0

-- The following private composition lemma is used only to assemble the actual
-- preparation/prefix/finish callbacks while carrying their derived invariant.
private abbrev Kernel (A : Type) := Cache F G → Bool → ProbComp ((A × Bool) × Cache F G)
private def Matches {A : Type} (oa : Source F G A) (pa : Kernel (F := F) (G := G) A) : Prop :=
  ∀ s live, Inv s live →
    (result <$> evaluate oa s live = pa s.cache s.bad) ∧
    ∀ out ∈ support (evaluate oa s live), Inv out.1.2 out.2

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem Matches.pure {A : Type} (a : A) :
    Matches (pure a : Source F G A) (fun cache bad => pure ((a,bad),cache)) := by
  intro s live hi
  constructor
  · simp [evaluate,runBallotOracle,result]
  · intro out ho
    simp only [evaluate,StateT.run_pure,runBallotOracle,simulateQ_pure,StateT.run_pure,
      support_pure,Set.mem_singleton_iff] at ho
    subst out
    exact hi

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem Matches.bind {A B : Type} {oa : Source F G A} {pa : Kernel (F := F) (G := G) A}
    (h : Matches oa pa) (next : A → Source F G B) (pn : A → Kernel (F := F) (G := G) B)
    (hn : ∀ a, Matches (next a) (pn a)) :
    Matches (oa >>= next) (fun cache bad => pa cache bad >>= fun out => pn out.1.1 out.2 out.1.2) := by
  intro s live hi
  obtain ⟨he,hpres⟩ := h s live hi
  constructor
  · simp only [evaluate,StateT.run_bind,runBallotOracle_bind,map_bind]
    rw [← he,bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro out ho
    exact (hn out.1.1 out.1.2 out.2 (hpres out ho)).1
  · intro out ho
    simp only [evaluate,StateT.run_bind,runBallotOracle_bind,support_bind,Set.mem_iUnion] at ho
    obtain ⟨mid,hm,ho⟩ := ho
    exact (hn mid.1.1 mid.1.2 mid.2 (hpres mid hm)).2 out ho

omit [Fintype F] [DecidableEq F] in
private theorem raw_matches {A : Type} (g pk : G) (oa : Comp F G A) :
    Matches (raw g pk oa) (fun cache bad => (fun out => ((out.1,bad),out.2)) <$> run oa cache) := by
  intro s live hi
  exact ⟨raw_runtime g pk oa s live hi,raw_inv g pk oa s live hi⟩

private theorem ballots_matches (g pk : G) (vote : Bool) :
    Matches (ballots (F := F) g pk vote) (fun cache bad => ElectionPrefixSimulation.ballotsSim g pk vote bad cache) := by
  intro s live hi
  exact ⟨ballots_runtime g pk vote s live hi,ballots_inv g pk vote s live hi⟩

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem trustee_matches {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool))
    (hp : ∀ cache out, out ∈ support (step.run cache) → project out.2 = project cache) :
    Matches (trustee step) (fun cache bad => (fun out => ((out.1.1,bad || out.1.2),out.2)) <$> step.run cache) := by
  intro s live hi
  constructor
  · simp only [trustee_evaluate,Functor.map_map,result]
  · exact trustee_inv step hp s live hi


/-- The actual prepared proof-simulation program, with fresh raw ballot queries
left explicit for replay. Preparation and all later callbacks share the state. -/
noncomputable def prepared {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    Source F G (PublicResult F G × Bool) := do
  let initial ← raw g 0 prepare
  let vote ← raw g 0 (liftProb (uniformSample Bool))
  let secret ← raw g 0 (liftProb (sampleNonzero F))
  let pk := secret • g
  let key ← trustee (TrusteeReachableSimulation.keySim g pk)
  let honest ← ballots g pk vote
  let before := ElectionPrefixSimulation.publication fingerprint g pk key honest
  let (submission,saved) ← raw g pk ((adversary initial).castBallot before)
  let cast ← raw g pk (liftBallot (repairedSubmitOracle g pk 2 before.board submission))
  let cts := boardTally cast.2
  let shares := fun j => partialDecrypt secret (cts j)
  let proofs ← trustee (ElectionTrusteeSimulation.simPair g pk cts shares)
  let view := ElectionTrusteeSimulation.publication before submission cast shares proofs
  let guess ← raw g pk ((adversary initial).guessVote saved view)
  pure (view,decide (guess = vote))

private theorem prepared_correct {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    (result <$> evaluate (prepared fingerprint g prepare adversary) .empty ∅ =
      ElectionFullSimulation.preparedSim fingerprint g prepare adversary) ∧
    ∀ out ∈ support (evaluate (prepared fingerprint g prepare adversary) .empty ∅),
      Inv out.1.2 out.2 := by
  have h := (raw_matches g 0 prepare).bind _ _ (fun initial =>
    (raw_matches g 0 (liftProb (uniformSample Bool))).bind _ _ (fun vote =>
    (raw_matches g 0 (liftProb (sampleNonzero F))).bind _ _ (fun secret =>
    (trustee_matches (TrusteeReachableSimulation.keySim (F := F) g (secret • g))
      (key_project g (secret • g))).bind _ _ (fun key =>
    (ballots_matches g (secret • g) vote).bind _ _ (fun honest =>
      let before := ElectionPrefixSimulation.publication fingerprint g (secret • g) key honest
      (raw_matches g (secret • g) ((adversary initial).castBallot before)).bind _ _ (fun made =>
      (raw_matches g (secret • g) (liftBallot
        (repairedSubmitOracle g (secret • g) 2 before.board made.1))).bind _ _ (fun cast =>
      let shares := fun j => partialDecrypt secret (boardTally cast.2 j)
      (trustee_matches (ElectionTrusteeSimulation.simPair g (secret • g) (boardTally cast.2) shares)
        (pair_project g (secret • g) (boardTally cast.2) shares)).bind _ _ (fun proofs =>
      let view := ElectionTrusteeSimulation.publication before made.1 cast shares proofs
      (raw_matches g (secret • g) ((adversary initial).guessVote made.2 view)).bind _ _ (fun guess =>
      Matches.pure (F := F) (G := G) (view,decide (guess = vote)))))))))))
  have hi : Inv (State.empty : State F G) ∅ := ⟨le_rfl,by simp [State.empty,State.ballot,project]⟩
  constructor
  · have he := (h .empty ∅ hi).1
    change result <$> evaluate (prepared fingerprint g prepare adversary) .empty ∅ = _ at he
    rw [he]
    simp only [State.empty,run_liftProb,bind_map_left,bind_assoc,pure_bind,
      Bool.false_or,ElectionFullSimulation.preparedSim,ElectionFullSimulation.worldSim,
      ElectionFullSimulation.afterSim,ElectionPrefixSimulation.sim]
    apply bind_congr
    intro initial
    apply bind_congr
    intro vote
    apply bind_congr
    intro secret
    apply bind_congr
    intro key
    change _ = ((fun out : (ElectionPrefixSimulation.Cast F G × Bool) × Cache F G =>
      ((ElectionPrefixSimulation.publication fingerprint g (secret • g) key.1.1 out.1.1,out.1.2),out.2)) <$>
        ElectionPrefixSimulation.ballotsSim g (secret • g) vote key.1.2 key.2) >>= _
    simp only [bind_map_left]
    apply bind_congr
    intro honest
    apply bind_congr
    intro made
    simp only [StateT.run,ElectionTrusteeSimulation.finishSim,bind_assoc,pure_bind]
    rfl
  · exact (h .empty ∅ hi).2

/-- Exact full-state correspondence to the composed statistical hybrid. The
empty initialization discharges the live/shadow invariant; no caller-supplied
cache or replay correspondence premise remains. -/
theorem prepared_runtime_eq {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    result <$> evaluate (prepared fingerprint g prepare adversary) .empty ∅ =
      ElectionFullSimulation.preparedSim fingerprint g prepare adversary :=
  (prepared_correct fingerprint g prepare adversary).1

/-- The complete actual prepared source derives its final live/shadow relation,
including after all casting, validation, trustee and guessing steps. -/
theorem prepared_inv {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : ((PublicResult F G × Bool) × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (prepared fingerprint g prepare adversary) .empty ∅)) :
    Inv out.1.2 out.2 := (prepared_correct fingerprint g prepare adversary).2 out ho

omit [Fintype F] [DecidableEq F] in
/-- Raw full-election callbacks cannot add a malicious statement to the honest
programming record. This supplies provenance for the next extraction obligation. -/
theorem raw_requests {A : Type} (g pk : G) (oa : Comp F G A) (s : State F G)
    (live : BallotOracleCache F G) (out : (A × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (raw g pk oa) s live)) :
    out.1.2.programmed = s.programmed := by
  rw [raw_evaluate,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  exact ballotProgrammed_raw_preserves_requests g pk _ s.ballot live mid hm


omit [Fintype F] [DecidableEq F] in
/-- A supported raw execution projects to the actual full-cache callback runtime. -/
theorem raw_support {A : Type} (g pk : G) (oa : Comp F G A) (s : State F G)
    (live : BallotOracleCache F G) (hi : Inv s live)
    (out : (A × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (raw g pk oa) s live)) :
    (out.1.1,out.1.2.cache) ∈ support (run oa s.cache) := by
  have hm : result out ∈ support (result <$> evaluate (raw g pk oa) s live) := by
    rw [support_map]; exact ⟨out,ho,rfl⟩
  rw [raw_runtime g pk oa s live hi,support_map] at hm
  obtain ⟨full,hf,he⟩ := hm
  have he' : full = (out.1.1,out.1.2.cache) := congrArg (fun z => (z.1.1,z.2)) he
  rwa [he'] at hf

private theorem ballots_targets (g pk : G) (vote : Bool) (s : State F G)
    (live : BallotOracleCache F G) (hempty : s.programmed = [])
    (out : (ElectionPrefixSimulation.Cast F G × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (ballots g pk vote) s live))
    (ha : out.1.1.1 = (.accepted,.accepted)) :
    ∀ stmt ∈ out.1.2.programmed, ∃ b ∈ out.1.1.2.map BoardEntry.ballot,
      ∃ i, stmt = b.coveredStatement g pk i := by
  rw [ballots_evaluate,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  exact repairedCastHonestPairOracle_programmed_targets_from g pk vote s.ballot live hempty mid hm ha

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
theorem trustee_requests {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool))
    (s : State F G) (live : BallotOracleCache F G)
    (out : (A × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (trustee step) s live)) :
    out.1.2.programmed = s.programmed := by
  rw [trustee_evaluate,support_map] at ho
  obtain ⟨mid,_,rfl⟩ := ho
  rfl

omit [Fintype F] in
theorem submit_live (g pk : G) (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (s : State F G) (live : BallotOracleCache F G) (hi : Inv s live)
    (ht : ∀ stmt ∈ s.programmed, ∃ old ∈ board.map BoardEntry.ballot,
      ∃ j, stmt = old.coveredStatement g pk j)
    (out : ((Decision × List (BoardEntry F G)) × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (raw g pk (liftBallot (repairedSubmitOracle g pk 2 board b))) s live))
    (ha : out.1.1.1 = .accepted) : b.CachedStrongValid g pk out.2 := by
  have hr := raw_support g pk _ s live hi out ho
  rw [liftBallot_run,support_map] at hr
  obtain ⟨actual,hactual,he⟩ := hr
  have hdecision : actual.1.1 = .accepted := (congrArg (fun z => z.1.1) he).trans ha
  obtain ⟨hv,hfresh,_⟩ := repairedSubmitOracle_accepted g pk 2 board b _ actual hactual hdecision
  have hcache : actual.2 = project out.1.2.cache := congrArg (fun z : (Decision × List (BoardEntry F G)) × Cache F G => project z.2) he
  rw [hcache] at hv
  have hfinal := raw_inv g pk _ s live hi out ho
  have hrecord := raw_requests g pk _ s live out ho
  intro i
  obtain ⟨c,hc,hvalid⟩ := hv i
  refine ⟨c,?_,hvalid⟩
  have hn : b.coveredStatement g pk i ∉ out.1.2.programmed := by
    rw [hrecord]
    intro hm
    obtain ⟨old,hold,j,he⟩ := ht _ hm
    exact hfresh old hold i j (congrArg BallotStatement.ciphertext he)
  exact (hfinal.2 _ hn).symm.trans hc

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
theorem evaluate_bind {A B : Type} (oa : Source F G A) (next : A → Source F G B)
    (s : State F G) (live : BallotOracleCache F G) :
    evaluate (oa >>= next) s live = (do
      let out ← evaluate oa s live
      evaluate (next out.1.1) out.1.2 out.2) := by
  simp only [evaluate,StateT.run_bind,runBallotOracle_bind]

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
theorem evaluate_pure {A : Type} (a : A) (s : State F G) (live : BallotOracleCache F G) :
    evaluate (pure a) s live = pure ((a,s),live) := by
  simp [evaluate,runBallotOracle]

/-- Every actually accepted malicious ballot in the complete replayable source
has all three full proofs valid in its final live cache, when both honest
prefix decisions accepted. Preparation, exclusion, cache consistency and later
preservation are derived from the supported execution. -/
theorem prepared_live {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : ((PublicResult F G × Bool) × State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (prepared fingerprint g prepare adversary) .empty ∅))
    (hhonest : out.1.1.1.beforeTally.honestDecisions = (.accepted,.accepted))
    (haccept : out.1.1.1.decision = .accepted) :
    out.1.1.1.submission.CachedStrongValid g out.1.1.1.beforeTally.parameters.publicKey out.2 := by
  simp only [prepared,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,vote,hvote,secret,hsecret,key,hkey,honest,hh,made,hm,cast,hcast,
    proofs,hproofs,guess,hguess,rfl⟩ := ho
  have hzero : Inv (State.empty : State F G) ∅ := ⟨le_rfl,by simp [State.empty,State.ballot,project]⟩
  have hii := raw_inv g 0 prepare .empty ∅ hzero initial hi
  have hvi := raw_inv g 0 _ _ _ hii vote hvote
  have hsi := raw_inv g 0 _ _ _ hvi secret hsecret
  have hki := trustee_inv _ (key_project g (secret.1.1 • g)) _ _ hsi key hkey
  have hhi := ballots_inv g (secret.1.1 • g) vote.1.1 _ _ hki honest hh
  have hmi := raw_inv g (secret.1.1 • g) _ _ _ hhi made hm
  have hinit := raw_requests g 0 prepare .empty ∅ initial hi
  have hvoteR := raw_requests g 0 _ _ _ vote hvote
  have hsecretR := raw_requests g 0 _ _ _ secret hsecret
  have hkeyR := trustee_requests _ _ _ key hkey
  have hempty : key.1.2.programmed = [] := hkeyR.trans (hsecretR.trans (hvoteR.trans hinit))
  have htargets := ballots_targets g (secret.1.1 • g) vote.1.1 _ _ hempty honest hh hhonest
  have hmadeR := raw_requests g (secret.1.1 • g) _ _ _ made hm
  have ht : ∀ stmt ∈ made.1.2.programmed, ∃ old ∈ honest.1.1.2.map BoardEntry.ballot,
      ∃ j, stmt = old.coveredStatement g (secret.1.1 • g) j := by
    simpa only [hmadeR] using htargets
  have hv := submit_live g (secret.1.1 • g) honest.1.1.2 made.1.1.1 _ _ hmi ht cast hcast haccept
  have hpersist := runBallotOracle_cache_le _ _ _ hproofs
  have hguessPersist := runBallotOracle_cache_le _ _ _ hguess
  exact hv.mono _ _ _ (hpersist.trans hguessPersist)


#print axioms key_inv
#print axioms trustee_requests
#print axioms submit_live
#print axioms evaluate_bind
#print axioms evaluate_pure
#print axioms raw_support
#print axioms raw_runtime
#print axioms raw_inv
#print axioms ballots_runtime
#print axioms ballots_inv
#print axioms prepared_runtime_eq
#print axioms prepared_inv
#print axioms raw_requests
#print axioms prepared_live
end ExplainableCrypto.Helios.Computational.ElectionProgrammedSource
