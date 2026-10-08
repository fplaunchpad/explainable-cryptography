import ExplainableCrypto.Helios.Computational.PrimeSubmission
import ExplainableCrypto.Helios.Computational.PrimeFullFieldSource

/-! Exact typed origin of the first programming call. No bit serialization claim. -/
namespace ExplainableCrypto.Helios.Computational.PrimeFirstProgramSource
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
variable {q : Nat} [Fact q.Prime] {G : Type} [AddCommGroup G]
  [Module (ZMod q) G] [DecidableEq G]

def run {A : Type}
    (g pk : G) (oa : OracleComp (BallotProofOracleSpec (ZMod q) G) A)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :=
  runBallotFiniteCache ((simulateQ (ballotFiniteProgrammedImpl g pk) oa).run state) live

theorem run_bind {A B : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec (ZMod q) G) A)
    (next : A → OracleComp (BallotProofOracleSpec (ZMod q) G) B)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :
    run g pk (oa >>= next) state live = (do
      let out ← run g pk oa state live
      run g pk (next out.1.1) out.1.2 out.2) := by
  simp [run,runBallotFiniteCache,simulateQ_bind,StateT.run_bind]

theorem run_lift {A : Type} (g pk : G) (oa : ProbComp A)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :
    run g pk (liftComp oa _) state live =
      (fun a => ((a,state),live)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [run,runBallotFiniteCache]
  | query_bind t next ih =>
    rw [liftComp_bind,run_bind]
    have hq : run g pk
        (liftComp (liftM (unifSpec.query t) : ProbComp _) _) state live =
        (fun a => ((a,state),live)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
      change run g pk
        (liftM ((BallotProofOracleSpec (ZMod q) G).query (.inl (.inl t)))) state live = _
      simp [run,runBallotFiniteCache,ballotFiniteProgrammedImpl,
        ballotFiniteProgrammedRaw,ballotFiniteCacheImpl,QueryImpl.add,StateT.run]
      change (fun a => ((a.1,state),a.2)) <$>
        ((fun a => (a,live)) <$> (liftM (unifSpec.query t) : ProbComp _)) = _
      rw [Functor.map_map]
    rw [hq]
    simp only [bind_map_left,map_bind]
    exact bind_congr ih



/-- Independent collision fixture: agreeing values do not suppress bad, and
an already recorded statement is prepended again. -/
def controlStatement : BallotStatement (ZMod 2) := ⟨0,0,(0,0)⟩
def controlTranscript : BallotCommitment (ZMod 2) × ZMod 2 × BallotResponse (ZMod 2) :=
  (((0,0),(0,0)),0,(0,0,0))
def controlOccupied : BallotFiniteProgrammedState (ZMod 2) (ZMod 2) :=
  ⟨(∅ : BallotFiniteCache (ZMod 2) (ZMod 2)).insert
    (controlStatement,controlTranscript.1) 0,false,[controlStatement]⟩

theorem control_collision :
    (controlOccupied.program controlStatement controlTranscript).2 =
      ⟨controlOccupied.cache,true,[controlStatement,controlStatement]⟩ := by
  have h : controlOccupied.cache.lookup (controlStatement,controlTranscript.1) = some 0 := by decide
  simp only [BallotFiniteProgrammedState.program,h]
  rfl

theorem control_collision_not_unchanged :
    (controlOccupied.program controlStatement controlTranscript).2 ≠ controlOccupied := by
  intro h
  have h' := congrArg BallotFiniteProgrammedState.bad h
  rw [control_collision] at h'
  contradiction

theorem control_fresh :
    ((BallotFiniteProgrammedState.empty : BallotFiniteProgrammedState (ZMod 2) (ZMod 2)).program
      controlStatement controlTranscript).2 =
      ⟨(∅ : BallotFiniteCache (ZMod 2) (ZMod 2)).insert
        (controlStatement,controlTranscript.1) 0,false,[controlStatement]⟩ := by
  simp [BallotFiniteProgrammedState.program,BallotFiniteProgrammedState.empty,controlTranscript]


omit [AddCommGroup G] [Module (ZMod q) G] in
/-- Private randomness preserves the complete live cache. -/
theorem live_lift {A : Type} (oa : ProbComp A)
    (live : BallotFiniteCache (ZMod q) G) :
    runBallotFiniteCache (liftComp oa (BallotOracleSpec (ZMod q) G)) live =
      (fun a => (a,live)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [runBallotFiniteCache]
  | query_bind t next ih =>
    simp only [liftComp_bind,runBallotFiniteCache,simulateQ_bind,StateT.run_bind]
    change ((fun a => (a,live)) <$> (liftM (unifSpec.query t) : ProbComp _)) >>=
      (fun out => runBallotFiniteCache (liftComp (next out.1) _) out.2) = _
    simp only [bind_map_left,ih,map_bind]

theorem request_run (g pk : G) (wit : BallotWitness (ZMod q))
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :
    run g pk (ballotProofQuery wit) state live =
      (fun t => (state.program (honestProofStatement g pk wit) t,live)) <$>
        ballotFullSimTranscript (F := ZMod q) (honestProofStatement g pk wit) := by
  simp only [run,ballotProofQuery,simulateQ_spec_query,ballotFiniteProgrammedImpl,QueryImpl.add,StateT.run]
  change runBallotFiniteCache (do
    let t ← liftComp (ballotFullSimTranscript (F := ZMod q) (honestProofStatement g pk wit)) _
    pure (state.program (honestProofStatement g pk wit) t)) live = _
  rw [show (do
    let t ← liftComp (ballotFullSimTranscript (F := ZMod q) (honestProofStatement g pk wit)) (BallotOracleSpec (ZMod q) G)
    pure (state.program (honestProofStatement g pk wit) t)) =
    liftComp ((state.program (honestProofStatement g pk wit)) <$>
      ballotFullSimTranscript (F := ZMod q) (honestProofStatement g pk wit)) _ by
      simp only [map_eq_bind_pure_comp,Function.comp_def,liftComp_bind,liftComp_pure]]
  rw [live_lift,Functor.map_map]


/-- First actual proof request, retaining an arbitrary original continuation.
The initial finite state is arbitrary; no freshness or consistency is assumed. -/
theorem first_program_bind {p : Nat} [Fact p.Prime] {A : Type}
    (g pk : PrimeGroup p q) (vote : Bool)
    (next : (ZMod q × ZMod q) → Proof01 (ZMod q) (PrimeGroup p q) →
      OracleComp (BallotProofOracleSpec (ZMod q) (PrimeGroup p q)) A)
    (state : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    run g pk (do
      let rs ← liftComp (drawPrimeNoncePair (q := q)) _
      let proof ← ballotProofQuery (vote,rs.1)
      next rs proof) state live = (do
      let rs ← drawPrimeNoncePair (q := q)
      let cs ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmt := honestProofStatement g pk (vote,rs.1)
      let t := (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2),
        cs.1,(cs.2.1,cs.2.2.1,cs.2.2.2))
      let out := state.program stmt t
      run g pk (next rs out.1) out.2 live) := by
  rw [run_bind,run_lift]
  simp only [bind_map_left]
  apply bind_congr
  intro rs
  rw [run_bind,request_run,PrimeFullFieldSource.ballotFullSimTranscript_factor]
  simp only [Functor.map_map,bind_map_left]

/-- The exact original continuation after Alice's first proof: two remaining
proof requests, verification, Bob's construction, attacker, and final submission. -/
def continuation (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (rs : ZMod q × ZMod q) (p0 : Proof01 (ZMod q) G) :
    OracleComp (BallotProofOracleSpec (ZMod q) G) (RepairedSubmissionResult (ZMod q) G) := do
  let p1 ← ballotProofQuery (false,rs.2)
  let pt ← ballotProofQuery (vote,rs.1+rs.2)
  let alice := assembleHonestBallot g pk vote rs p0 p1 pt
  let first ← liftComp (repairedSubmitOracle g pk 0 [] alice) _
  let rs1 ← liftComp (drawPrimeNoncePair (q := q)) _
  let bob ← strongHonestBallotWithNoncesOracle g pk (!vote) rs1
  let second ← liftComp (repairedSubmitOracle g pk 1 first.2 bob) _
  let honest := ((first.1,second.1),second.2)
  let ballot ← liftComp (attacker honest) _
  let cast ← liftComp (repairedSubmitOracle g pk 2 honest.2 ballot) _
  pure ⟨honest,ballot,cast.1,cast.2⟩

/-- Syntactic factoring of the actual source, including every rejection branch. -/
theorem source_eq (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    repairedSubmissionPrimeOracle g pk vote attacker = (do
      let rs ← liftComp (drawPrimeNoncePair (q := q)) _
      let p0 ← ballotProofQuery (vote,rs.1)
      continuation g pk vote attacker rs p0) := by
  simp only [repairedSubmissionPrimeOracle,repairedSubmissionWithNoncePairs,
    strongHonestBallotWithNoncesOracle,continuation,bind_assoc,pure_bind]


/-- Exact complete finite source decomposition at its first programming call. -/
theorem submission_run {p : Nat} [Fact p.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (state : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    run g pk (repairedSubmissionPrimeOracle g pk vote attacker) state live = (do
      let rs ← drawPrimeNoncePair (q := q)
      let cs ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmt := honestProofStatement g pk (vote,rs.1)
      let t := (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2),
        cs.1,(cs.2.1,cs.2.2.1,cs.2.2.2))
      let out := state.program stmt t
      run g pk (continuation g pk vote attacker rs out.1) out.2 live) := by
  rw [source_eq]
  exact first_program_bind g pk vote (continuation g pk vote attacker) state live

/-- Empty initialization is a specialization, not a premise for arbitrary callers. -/
theorem submission_empty {p : Nat} [Fact p.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2)) :
    runBallotFiniteProgrammed g pk (repairedSubmissionPrimeOracle g pk vote attacker) = (do
      let rs ← drawPrimeNoncePair (q := q)
      let cs ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmt := honestProofStatement g pk (vote,rs.1)
      let t := (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2),
        cs.1,(cs.2.1,cs.2.2.1,cs.2.2.2))
      let out := BallotFiniteProgrammedState.empty.program stmt t
      run g pk (continuation g pk vote attacker rs out.1) out.2 ∅) :=
  submission_run g pk vote attacker .empty ∅

#print axioms run_bind
#print axioms run_lift
#print axioms live_lift
#print axioms request_run
#print axioms first_program_bind
#print axioms source_eq
#print axioms submission_run
#print axioms submission_empty
#print axioms control_collision
#print axioms control_collision_not_unchanged
#print axioms control_fresh
end ExplainableCrypto.Helios.Computational.PrimeFirstProgramSource
