import ExplainableCrypto.Helios.Computational.ElectionDDHConstruction
import ExplainableCrypto.Helios.Computational.ElectionProgrammedSource
import ExplainableCrypto.Helios.Computational.ElectionQueryBound

/-! Honest challenge ballots use the existing statement programmer and actual
repaired submissions. Fixed-nonce equations preserve source trees; sampling
schedule equations below concern interpreted distributions only. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionDDHConstruction
variable {F G : Type} [Field F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev BallotSource (F G : Type) := StateT (BallotProgrammedState F G) (BallotOracleComp F G)
abbrev Cast (F G : Type) := (Decision × Decision) × List (BoardEntry F G)

/-- All three actual ciphertext statements are programmed, including the
implicit aggregate. There is no witness input. -/
def ballot (g pk : G) (cts : Fin 2 → Ciphertext G) : BallotSource F G (Ballot F G 2) := do
  let p0 ← ballotProgrammedStatement ⟨g,pk,cts 0⟩
  let p1 ← ballotProgrammedStatement ⟨g,pk,cts 1⟩
  let pt ← ballotProgrammedStatement ⟨g,pk,cts 0 + cts 1⟩
  pure ⟨cts,![p0,p1],pt⟩

/-- Use the existing repaired submission, including short-circuit verification
and the board retained after either rejection. -/
def submit (g pk : G) (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    BallotSource F G (Decision × List (BoardEntry F G)) :=
  simulateQ (ballotProgrammedImpl g pk)
    (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec F G))

def honestPair (g pk : G) (cts : Pair G) : BallotSource F G (Cast F G) := do
  let alice ← ballot g pk cts.1
  let first ← submit g pk 0 [] alice
  let bob ← ballot g pk cts.2
  let second ← submit g pk 1 first.2 bob
  pure ((first.1,second.1),second.2)

/-- The reference is the actual old proof requests and repaired submissions
with only the four nonce draws exposed as parameters. -/
def withNonces (g pk : G) (vote : Bool) (rs ss : F × F) :
    OracleComp (BallotProofOracleSpec F G) (Cast F G) := do
  let alice ← strongHonestBallotWithNoncesOracle g pk vote rs
  let first ← liftComp (repairedSubmitOracle g pk 0 [] alice) _
  let bob ← strongHonestBallotWithNoncesOracle g pk (!vote) ss
  let second ← liftComp (repairedSubmitOracle g pk 1 first.2 bob) _
  pure ((first.1,second.1),second.2)

omit [DecidableEq F] in
/-- Exact source identity for a real honest ballot, including aggregate requests
and all successor programming states, from any initial cache/flag/record. -/
theorem ballot_real (g pk : G) (vote : Bool) (rs : F × F) :
    ballot g pk ![encryptWith g pk rs.1 (voteScalar vote),encryptWith g pk rs.2 0] =
      simulateQ (ballotProgrammedImpl g pk) (strongHonestBallotWithNoncesOracle g pk vote rs) := by
  simp only [ballot,strongHonestBallotWithNoncesOracle,ballotProofQuery,
    simulateQ_bind,simulateQ_pure,simulateQ_spec_query,ballotProgrammedImpl_statement,
    Matrix.cons_val_zero,Matrix.cons_val_one,encryptWith_add,add_zero]
  rfl

/-- Fixed-nonce equality uses the original query computation, not merely the
law of its result. Both actual submission decisions and caches are retained. -/
theorem honest_pair_real (g pk : G) (vote : Bool) (rs ss : F × F) :
    honestPair g pk (paired g pk (rs.1 • g) (rs.1 • pk)
      (rs.1 + ss.1) rs.2 ss.2 vote).1 =
      simulateQ (ballotProgrammedImpl g pk) (withNonces g pk vote rs ss) := by
  rw [paired_real]
  simp only [honestPair,original,ballot_real,withNonces,simulateQ_bind,simulateQ_pure,submit]

/-- The reduction retains the known column nonce sums alongside the original
submission result. They are private construction state. -/
def challengePair (g pk A T : G) (total a b : F) (vote : Bool) :
    BallotSource F G (Cast F G × (Fin 2 → F)) := do
  let out := paired g pk A T total a b vote
  let cast ← honestPair g pk out.1
  pure (cast,out.2)

/-- Source equality before interpreting live hashes, with known nonce sums. -/
theorem challenge_pair_real (g pk : G) (vote : Bool) (rs ss : F × F) :
    challengePair g pk (rs.1 • g) (rs.1 • pk) (rs.1 + ss.1) rs.2 ss.2 vote =
      (do let cast ← simulateQ (ballotProgrammedImpl g pk) (withNonces g pk vote rs ss)
          pure (cast,![rs.1+ss.1,rs.2+ss.2])) := by
  dsimp only [challengePair]
  rw [honest_pair_real]
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem run_pure {A : Type} (a : A) (live : BallotOracleCache F G) :
    runBallotOracle (pure a) live = pure (a,live) := by simp [runBallotOracle]

omit [DecidableEq F] in
/-- Invariant preservation for arbitrary challenge ciphertexts, without a real
witness or acceptance premise. -/
theorem ballot_inv (g pk : G) (cts : Fin 2 → Ciphertext G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv s live)
    (out : (Ballot F G 2 × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((ballot g pk cts).run s) live)) :
    BallotProgrammedInv out.1.2 out.2 := by
  simp only [ballot,StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  exact ballotProgrammedStatement_inv _ _ _
    (ballotProgrammedStatement_inv _ _ _ (ballotProgrammedStatement_inv _ _ _ hi a ha) b hb) c hc

/-- Both actual submissions preserve live/shadow consistency, including every
invalid-proof and reused-ciphertext branch of arbitrary challenge inputs. -/
theorem honest_pair_inv (g pk : G) (cts : Pair G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv s live)
    (out : (Cast F G × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((honestPair g pk cts).run s) live)) :
    BallotProgrammedInv out.1.2 out.2 := by
  simp only [honestPair,StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,first,hfirst,b,hb,second,hsecond,rfl⟩ := ho
  have h1 := ballot_inv g pk cts.1 s live hi a ha
  have h2 := ballotProgrammed_preserves_inv_of_inv g pk _ _ _ h1 first hfirst
  have h3 := ballot_inv g pk cts.2 first.1.2 first.2 h2 b hb
  exact ballotProgrammed_preserves_inv_of_inv g pk _ _ _ h3 second hsecond

variable [Fintype F]

/-- Original interleaved nonce schedule with private sums retained. Forgetting
those sums recovers the unchanged sampled honest source. -/
noncomputable def sampledWithSums (g pk : G) (vote : Bool) :
    OracleComp (BallotProofOracleSpec F G) (Cast F G × (Fin 2 → F)) := do
  let rs ← liftComp (drawNoncePair F) _
  let alice ← strongHonestBallotWithNoncesOracle g pk vote rs
  let first ← liftComp (repairedSubmitOracle g pk 0 [] alice) _
  let ss ← liftComp (drawNoncePair F) _
  let bob ← strongHonestBallotWithNoncesOracle g pk (!vote) ss
  let second ← liftComp (repairedSubmitOracle g pk 1 first.2 bob) _
  pure (((first.1,second.1),second.2),![rs.1+ss.1,rs.2+ss.2])

omit [SampleableType F] in
/-- Exact source projection, retaining every original hash/proof request. -/
theorem sampledWithSums_fst (g pk : G) (vote : Bool) :
    Prod.fst <$> sampledWithSums (F := F) g pk vote = repairedCastHonestPairOracle g pk vote := by
  simp only [sampledWithSums,repairedCastHonestPairOracle,strongHonestBallotOracle,
    map_bind,map_pure,bind_assoc]

omit [Fintype F] [DecidableEq F] in
/-- Independent probability draws preserve the full programmed state and live cache. -/
theorem run_programmed_prob {A : Type} (g pk : G) (oa : ProbComp A)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (liftComp oa (BallotProofOracleSpec F G))).run s) live =
      (fun x => ((x,s),live)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing s live with
  | pure x => simp [runBallotOracle]
  | query_bind t next ih =>
    rw [liftComp_bind,runProgrammed_bind]
    have hq : runBallotOracle ((simulateQ (ballotProgrammedImpl (F := F) g pk)
        (liftComp (liftM (unifSpec.query t) : ProbComp _) (BallotProofOracleSpec F G))).run s) live =
        (fun u => ((u,s),live)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
      change runBallotOracle (do
        let u ← liftComp (liftM (unifSpec.query t) : ProbComp _) (BallotOracleSpec F G)
        pure (u,s)) live = _
      rw [runBallotOracle_lift_bind]
      simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp]
    rw [hq]
    simp only [bind_map_left,ih,map_bind]

/-- Front-loading the independent Bob nonce pair preserves interpreted output
laws and both caches. It does not assert equality of source query trees. -/
theorem sampledWithSums_schedule (g pk : G) (vote : Bool)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    𝒮[runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (sampledWithSums g pk vote)).run s) live] =
    𝒮[do let rs ← drawNoncePair F; let ss ← drawNoncePair F
         let out ← runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
           (withNonces g pk vote rs ss)).run s) live
         pure (((out.1.1,![rs.1+ss.1,rs.2+ss.2]),out.1.2),out.2)] := by
  simp only [sampledWithSums,withNonces,runProgrammed_bind,run_programmed_prob,
    runProgrammed_pure,bind_map_left,bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro rs
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext alice
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs => rw [evalSPMF_bind_bind_swap]

/-- The four-nonce loss now covers actual submissions and complete successor
state, including both rejection decisions and live cache. Private sums remain
available to the reduction. No fresh/empty-cache premise is imposed. -/
theorem honest_pair_real_distance_le (g pk : G) (vote : Bool)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    tvDist
      (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
        (sampledWithSums g pk vote)).run s) live)
      (do let x ← uniformSample F; let a ← uniformSample F
          let t ← uniformSample F; let b ← uniformSample F
          runBallotOracle ((challengePair g pk (x • g) (x • pk) t a b vote).run s) live) ≤
      4 * (Fintype.card F : ℝ)⁻¹ := by
  let next := fun input : Output F G => do
    let out ← runBallotOracle ((honestPair g pk input.1).run s) live
    pure (((out.1.1,input.2),out.1.2),out.2)
  let nz := do
    let x ← sampleNonzero F; let a ← sampleNonzero F
    let y ← sampleNonzero F; let b ← sampleNonzero F
    pure (original g pk x a y b vote)
  let full := do
    let x ← uniformSample F; let a ← uniformSample F
    let t ← uniformSample F; let b ← uniformSample F
    pure (paired g pk (x • g) (x • pk) t a b vote)
  have hs : 𝒮[runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (sampledWithSums g pk vote)).run s) live] = 𝒮[nz >>= next] := by
    rw [sampledWithSums_schedule]
    simp only [nz,drawNoncePair,bind_assoc,pure_bind]
    apply evalSPMF_bind_congr'; intro x
    apply evalSPMF_bind_congr'; intro a
    apply evalSPMF_bind_congr'; intro y
    apply evalSPMF_bind_congr'; intro b
    have he := honest_pair_real g pk vote (x,a) (y,b)
    rw [paired_real] at he
    dsimp only at he
    dsimp only [next]
    rw [he]
    rfl
  have ht : 𝒮[do
      let x ← uniformSample F; let a ← uniformSample F
      let t ← uniformSample F; let b ← uniformSample F
      runBallotOracle ((challengePair g pk (x • g) (x • pk) t a b vote).run s) live] =
      𝒮[full >>= next] := by
    simp only [full,bind_assoc,pure_bind]
    apply evalSPMF_bind_congr'; intro x
    apply evalSPMF_bind_congr'; intro a
    apply evalSPMF_bind_congr'; intro t
    apply evalSPMF_bind_congr'; intro b
    dsimp only [challengePair]
    simp only [StateT.run_bind,StateT.run_pure]
    rw [runBallotOracle_bind]
    simp [next,runBallotOracle]
  have h := (tvDist_bind_right_le next nz full).trans
    (paired_ciphertexts_nonzero_distance_le g pk vote)
  unfold tvDist at h ⊢
  rw [hs,ht]
  exact h

/-- Embed the challenge pair in the existing full election state. Auxiliary
key/trustee entries are preserved by the existing `rebuild` operation. -/
def ballots (g pk A T : G) (total a b : F) (vote : Bool) :
    ElectionProgrammedSource.Source F G (Cast F G × (Fin 2 → F)) := fun s => do
  let out ← (challengePair g pk A T total a b vote).run s.ballot
  pure (out.1,ElectionProgrammedSource.rebuild s.cache out.2)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [Fintype F] in
private theorem full_run {A : Type} (step : BallotSource F G A)
    (s : ElectionProgrammedSource.State F G) (live : BallotOracleCache F G) :
    ElectionProgrammedSource.evaluate (fun s => do
      let out ← step.run s.ballot
      pure (out.1,ElectionProgrammedSource.rebuild s.cache out.2)) s live =
      (fun out => ((out.1.1,ElectionProgrammedSource.rebuild s.cache out.1.2),out.2)) <$>
        runBallotOracle (step.run s.ballot) live := by
  change runBallotOracle (do
    let out ← step.run s.ballot
    pure (out.1,ElectionProgrammedSource.rebuild s.cache out.2)) live = _
  rw [runBallotOracle_bind]
  simp only [run_pure,bind_pure_comp]

/-- Full-cache version of the actual historical honest-prefix comparison.
Only the newly retained private sums are projected away. -/
theorem ballots_real_distance_le (g pk : G) (vote : Bool)
    (s : ElectionProgrammedSource.State F G) (live : BallotOracleCache F G) :
    tvDist (ElectionProgrammedSource.evaluate (ElectionProgrammedSource.ballots g pk vote) s live)
      ((fun out => ((out.1.1.1,out.1.2),out.2)) <$>
        (do let x ← uniformSample F; let a ← uniformSample F
            let t ← uniformSample F; let b ← uniformSample F
            ElectionProgrammedSource.evaluate (ballots g pk (x • g) (x • pk) t a b vote) s live)) ≤
      4 * (Fintype.card F : ℝ)⁻¹ := by
  let restore := fun out : ((Cast F G × (Fin 2 → F)) × BallotProgrammedState F G) ×
      BallotOracleCache F G => ((out.1.1.1,ElectionProgrammedSource.rebuild s.cache out.1.2),out.2)
  have h := (tvDist_map_le restore _ _).trans (honest_pair_real_distance_le g pk vote s.ballot live)
  have he := congrArg (fun oa => (fun out =>
      ((out.1.1,ElectionProgrammedSource.rebuild s.cache out.1.2),out.2)) <$>
      runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) oa).run s.ballot) live)
    (sampledWithSums_fst (F := F) g pk vote)
  have old_run := full_run (simulateQ (ballotProgrammedImpl g pk)
    (repairedCastHonestPairOracle g pk vote)) s live
  change ElectionProgrammedSource.evaluate (ElectionProgrammedSource.ballots g pk vote) s live = _ at old_run
  have hl : restore <$> runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (sampledWithSums g pk vote)).run s.ballot) live =
      ElectionProgrammedSource.evaluate (ElectionProgrammedSource.ballots g pk vote) s live := by
    rw [old_run]
    simpa only [restore,simulateQ_map,StateT.run_map,runBallotOracle,Functor.map_map,
      Function.comp_def,Prod.map] using he
  rw [hl] at h
  have hr : restore <$> (do
      let x ← uniformSample F; let a ← uniformSample F
      let t ← uniformSample F; let b ← uniformSample F
      runBallotOracle ((challengePair g pk (x • g) (x • pk) t a b vote).run s.ballot) live) =
      (fun out => ((out.1.1.1,out.1.2),out.2)) <$>
        (do let x ← uniformSample F; let a ← uniformSample F
            let t ← uniformSample F; let b ← uniformSample F
            ElectionProgrammedSource.evaluate (ballots g pk (x • g) (x • pk) t a b vote) s live) := by
    simp only [map_bind]
    apply bind_congr; intro x
    apply bind_congr; intro a
    apply bind_congr; intro t
    apply bind_congr; intro b
    have new_run := full_run (challengePair g pk (x • g) (x • pk) t a b vote) s live
    change ElectionProgrammedSource.evaluate (ballots g pk (x • g) (x • pk) t a b vote) s live = _ at new_run
    rw [new_run]
    simp only [restore,Functor.map_map]
  rw [hr] at h
  exact h

omit [Fintype F] in
/-- The actual full-state wrapper preserves the cache invariant even for
random challenge inputs and rejected honest ballots. -/
theorem ballots_inv (g pk A T : G) (total a b : F) (vote : Bool)
    (s : ElectionProgrammedSource.State F G) (live : BallotOracleCache F G)
    (hi : ElectionProgrammedSource.Inv s live)
    (out : ((Cast F G × (Fin 2 → F)) × ElectionProgrammedSource.State F G) × BallotOracleCache F G)
    (ho : out ∈ support (ElectionProgrammedSource.evaluate
      (ballots g pk A T total a b vote) s live)) :
    ElectionProgrammedSource.Inv out.1.2 out.2 := by
  have he := full_run (challengePair g pk A T total a b vote) s live
  change ElectionProgrammedSource.evaluate (ballots g pk A T total a b vote) s live = _ at he
  rw [he,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  dsimp only [challengePair] at hm
  simp only [StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hm
  obtain ⟨cast,hcast,rfl⟩ := hm
  have h := honest_pair_inv g pk (paired g pk A T total a b vote).1 s.ballot live hi cast hcast
  simpa only [ElectionProgrammedSource.Inv,ElectionProgrammedSource.rebuild,
    ElectionProgrammedSource.State.ballot,ElectionCache.project_replace] using h

omit [Fintype F] [DecidableEq F] in
private theorem statement_requests (stmt : BallotStatement G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (Proof01 F G × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((ballotProgrammedStatement stmt).run s) live)) :
    out.1.2.programmed = stmt :: s.programmed := by
  rw [ballotProgrammedStatement_runtime,support_map] at ho
  obtain ⟨mid,_,rfl⟩ := ho
  rfl

omit [Fintype F] [DecidableEq F] in
/-- All recorded targets are the actual returned ballot's covered statements,
including its aggregate, even for challenge ciphertexts without known witnesses. -/
theorem ballot_targets (g pk : G) (cts : Fin 2 → Ciphertext G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (Ballot F G 2 × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((ballot g pk cts).run s) live)) :
    out.1.2.programmed = [out.1.1.coveredStatement g pk none,
      out.1.1.coveredStatement g pk (some 1),out.1.1.coveredStatement g pk (some 0)] ++ s.programmed := by
  simp only [ballot,StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  have h1 := statement_requests _ _ _ a ha
  have h2 := statement_requests _ _ _ b hb
  have h3 := statement_requests _ _ _ c hc
  simpa [Ballot.coveredStatement,Ballot.coveredCiphertext,Ballot.aggregate,
    Fin.sum_univ_two,h1,h2] using h3

omit [Fintype F] in
/-- Both actual acceptances put every newly programmed target on the retained
board. The empty incoming record will be derived by the prepared prefix. -/
theorem honest_pair_targets (g pk : G) (cts : Pair G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hempty : s.programmed = [])
    (out : (Cast F G × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((honestPair g pk cts).run s) live))
    (ha : out.1.1.1 = (.accepted,.accepted)) :
    ∀ stmt ∈ out.1.2.programmed, ∃ b ∈ out.1.1.2.map BoardEntry.ballot,
      ∃ i, stmt = b.coveredStatement g pk i := by
  simp only [honestPair,StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨alice,halice,first,hfirst,bob,hbob,second,hsecond,rfl⟩ := ho
  have hfirstB := (programmed_submit_accepted g pk 0 [] alice.1.1 _ _ first hfirst (congrArg Prod.fst ha)).2
  have hsecondB := (programmed_submit_accepted g pk 1 first.1.1.2 bob.1.1 _ _ second hsecond (congrArg Prod.snd ha)).2
  have haliceL := ballot_targets g pk cts.1 s live alice halice
  have hfirstL := ballotProgrammed_raw_preserves_requests g pk _ _ _ first hfirst
  have hbobL := ballot_targets g pk cts.2 _ _ bob hbob
  have hsecondL := ballotProgrammed_raw_preserves_requests g pk _ _ _ second hsecond
  intro stmt hmem
  simp only [hsecondL,hbobL,hfirstL,haliceL,hempty,
    List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hmem
  have hb : second.1.1.2.map BoardEntry.ballot = [alice.1.1,bob.1.1] := by
    simp [hsecondB,hfirstB]
  rcases hmem with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact ⟨bob.1.1,by simp [hb],none,rfl⟩
  · exact ⟨bob.1.1,by simp [hb],some 1,rfl⟩
  · exact ⟨bob.1.1,by simp [hb],some 0,rfl⟩
  · exact ⟨alice.1.1,by simp [hb],none,rfl⟩
  · exact ⟨alice.1.1,by simp [hb],some 1,rfl⟩
  · exact ⟨alice.1.1,by simp [hb],some 0,rfl⟩

omit [Fintype F] in
/-- Provenance in the actual full cache wrapper, with the private sums retained. -/
theorem ballots_targets (g pk A T : G) (total a b : F) (vote : Bool)
    (s : ElectionProgrammedSource.State F G) (live : BallotOracleCache F G)
    (hempty : s.programmed = [])
    (out : ((Cast F G × (Fin 2 → F)) × ElectionProgrammedSource.State F G) × BallotOracleCache F G)
    (ho : out ∈ support (ElectionProgrammedSource.evaluate (ballots g pk A T total a b vote) s live))
    (ha : out.1.1.1.1 = (.accepted,.accepted)) :
    ∀ stmt ∈ out.1.2.programmed, ∃ old ∈ out.1.1.1.2.map BoardEntry.ballot,
      ∃ i, stmt = old.coveredStatement g pk i := by
  have he := full_run (challengePair g pk A T total a b vote) s live
  change ElectionProgrammedSource.evaluate (ballots g pk A T total a b vote) s live = _ at he
  rw [he,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  dsimp only [challengePair] at hm
  simp only [StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hm
  obtain ⟨cast,hcast,rfl⟩ := hm
  exact honest_pair_targets g pk _ s.ballot live hempty cast hcast ha

omit [Fintype F] [DecidableEq F] in
private theorem ballot_ciphertexts (g pk : G) (cts : Fin 2 → Ciphertext G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (Ballot F G 2 × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((ballot g pk cts).run s) live)) :
    out.1.1.ciphertext = cts := by
  simp only [ballot,StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  rfl

omit [Fintype F] in
private theorem honest_pair_columns (g pk : G) (cts : Pair G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (Cast F G × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((honestPair g pk cts).run s) live))
    (ha : out.1.1.1 = (.accepted,.accepted)) (i : Fin 2) :
    boardTally out.1.1.2 i = cts.1 i + cts.2 i := by
  simp only [honestPair,StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨alice,halice,first,hfirst,bob,hbob,second,hsecond,rfl⟩ := ho
  have hfirstB := (programmed_submit_accepted g pk 0 [] alice.1.1 _ _ first hfirst (congrArg Prod.fst ha)).2
  have hsecondB := (programmed_submit_accepted g pk 1 first.1.1.2 bob.1.1 _ _ second hsecond (congrArg Prod.snd ha)).2
  have haliceC := ballot_ciphertexts g pk cts.1 s live alice halice
  have hbobC := ballot_ciphertexts g pk cts.2 _ _ bob hbob
  simp [boardTally,hsecondB,hfirstB,haliceC,hbobC]

omit [Fintype F] in
/-- Both actual honest acceptances derive the column encryption from the
retained nonce sums. This holds for arbitrary challenge inputs and incoming
state; board shape, freshness and cache consistency are not supplied premises. -/
theorem ballots_columns (g pk A T : G) (total a b : F) (vote : Bool)
    (s : ElectionProgrammedSource.State F G) (live : BallotOracleCache F G)
    (out : ((Cast F G × (Fin 2 → F)) × ElectionProgrammedSource.State F G) × BallotOracleCache F G)
    (ho : out ∈ support (ElectionProgrammedSource.evaluate (ballots g pk A T total a b vote) s live))
    (ha : out.1.1.1.1 = (.accepted,.accepted)) (i : Fin 2) :
    boardTally out.1.1.1.2 i = encryptWith g pk (out.1.1.2 i) (if i = 0 then 1 else 0) := by
  have he := full_run (challengePair g pk A T total a b vote) s live
  change ElectionProgrammedSource.evaluate (ballots g pk A T total a b vote) s live = _ at he
  rw [he,support_map] at ho
  obtain ⟨mid,hm,rfl⟩ := ho
  dsimp only [challengePair] at hm
  simp only [StateT.run_bind,StateT.run_pure,runBallotOracle_bind,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hm
  obtain ⟨cast,hcast,rfl⟩ := hm
  exact (honest_pair_columns g pk _ s.ballot live cast hcast ha i).trans
    (paired_totals g pk A T total a b vote i)

omit [Fintype F] [DecidableEq F] in
private theorem ballot_bound (g pk : G) (cts : Fin 2 → Ciphertext G) (s : BallotProgrammedState F G) :
    ((ballot g pk cts).run s).IsQueryBoundP (isBallotHashQuery (F := F)) 0 := by
  simp only [ballot,StateT.run_bind,StateT.run_pure]
  apply isQueryBoundP_bind (n := 0) (m := 0) (ballotProgrammedStatement_query_bound _ _)
  intro a _
  apply isQueryBoundP_bind (n := 0) (m := 0) (ballotProgrammedStatement_query_bound _ _)
  intro b _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using ballotProgrammedStatement_query_bound (F := F)
    (⟨g,pk,cts 0 + cts 1⟩ : BallotStatement G) b.2

private theorem submit_bound (g pk : G) (voter : Fin 3) (board : List (BoardEntry F G))
    (b : Ballot F G 2) (s : BallotProgrammedState F G) :
    ((submit g pk voter board b).run s).IsQueryBoundP (isBallotHashQuery (F := F)) 3 :=
  ballotProgrammed_query_bound g pk _ 3
    (raw_lift_hash_bound _ 3 (ElectionQueryBound.submit_bound g pk voter board b)) s

private theorem honest_pair_bound (g pk : G) (cts : Pair G) (s : BallotProgrammedState F G) :
    ((honestPair g pk cts).run s).IsQueryBoundP (isBallotHashQuery (F := F)) 6 := by
  simp only [honestPair,StateT.run_bind,StateT.run_pure]
  apply isQueryBoundP_bind (n := 0) (m := 6) (ballot_bound g pk cts.1 s)
  intro a _
  apply isQueryBoundP_bind (n := 3) (m := 3) (submit_bound g pk 0 [] a.1 a.2)
  intro first _
  apply isQueryBoundP_bind (n := 0) (m := 3) (ballot_bound g pk cts.2 first.2)
  intro b _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using submit_bound g pk 1 first.1.2 b.1 b.2

/-- Both actual verifications issue at most six live hashes; proof programming
uses private coins. This budget covers every rejection branch. -/
theorem ballots_bound (g pk A T : G) (total a b : F) (vote : Bool)
    (s : ElectionProgrammedSource.State F G) :
    ((ballots g pk A T total a b vote).run s).IsQueryBoundP (isBallotHashQuery (F := F)) 6 := by
  change (do let out ← (challengePair g pk A T total a b vote).run s.ballot
             pure (out.1,ElectionProgrammedSource.rebuild s.cache out.2)).IsQueryBoundP _ 6
  rw [bind_pure_comp,isQueryBoundP_map_iff]
  dsimp only [challengePair]
  rw [StateT.run_bind]
  simpa only [StateT.run_pure,bind_pure_comp,isQueryBoundP_map_iff] using
    honest_pair_bound g pk (paired g pk A T total a b vote).1 s.ballot


#print axioms ballots_columns
#print axioms run_programmed_prob
#print axioms ballot_targets
#print axioms honest_pair_targets
#print axioms ballots_targets
#print axioms ballots_bound
#print axioms ballots_inv
#print axioms ballots_real_distance_le
#print axioms ballot_inv
#print axioms honest_pair_inv
#print axioms honest_pair_real_distance_le
#print axioms sampledWithSums_schedule
#print axioms ballot_real
#print axioms honest_pair_real
#print axioms challenge_pair_real
#print axioms sampledWithSums_fst
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
