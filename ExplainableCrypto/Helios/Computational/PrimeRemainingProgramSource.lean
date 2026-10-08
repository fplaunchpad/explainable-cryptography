import ExplainableCrypto.Helios.Computational.PrimeFirstProgramSource

namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSource
open OracleComp OracleSpec PrimeFirstProgramSource
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

/-- Exact source body after Alice's three proof requests, including all verification
and rejection behavior, Bob's constructor, attacker and final submission. -/
def afterAliceProofs (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (rs : ZMod q × ZMod q) (p0 p1 pt : Proof01 (ZMod q) (PrimeGroup p q)) :
    OracleComp (BallotProofOracleSpec (ZMod q) (PrimeGroup p q))
      (RepairedSubmissionResult (ZMod q) (PrimeGroup p q)) := do
  let alice := assembleHonestBallot g pk vote rs p0 p1 pt
  let first ← liftComp (repairedSubmitOracle g pk 0 [] alice) _
  let rs1 ← liftComp (drawPrimeNoncePair (q := q)) _
  let bob ← strongHonestBallotWithNoncesOracle g pk (!vote) rs1
  let second ← liftComp (repairedSubmitOracle g pk 1 first.2 bob) _
  let honest := ((first.1,second.1),second.2)
  let ballot ← liftComp (attacker honest) _
  let cast ← liftComp (repairedSubmitOracle g pk 2 honest.2 ballot) _
  pure ⟨honest,ballot,cast.1,cast.2⟩

/-- Two actual programming requests in their source order. The first proof, states
and remaining continuation are arbitrary; each request has fresh full-field draws. -/
theorem remaining_program_bind {A : Type}
    (g pk : PrimeGroup p q) (vote : Bool) (rs : ZMod q × ZMod q)
    (p0 : Proof01 (ZMod q) (PrimeGroup p q))
    (next : Proof01 (ZMod q) (PrimeGroup p q) → Proof01 (ZMod q) (PrimeGroup p q) →
      Proof01 (ZMod q) (PrimeGroup p q) →
      OracleComp (BallotProofOracleSpec (ZMod q) (PrimeGroup p q)) A)
    (state : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    run g pk (do
      let p1 ← ballotProofQuery (false,rs.2)
      let pt ← ballotProofQuery (vote,rs.1+rs.2)
      next p0 p1 pt) state live = (do
      let cs1 ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmt1 := honestProofStatement g pk (false,rs.2)
      let tr1 := (ballotSimCommit stmt1 cs1.1 (cs1.2.1,cs1.2.2.1,cs1.2.2.2),
        cs1.1,(cs1.2.1,cs1.2.2.1,cs1.2.2.2))
      let out1 := state.program stmt1 tr1
      let csT ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmtT := honestProofStatement g pk (vote,rs.1+rs.2)
      let trT := (ballotSimCommit stmtT csT.1 (csT.2.1,csT.2.2.1,csT.2.2.2),
        csT.1,(csT.2.1,csT.2.2.1,csT.2.2.2))
      let outT := out1.2.program stmtT trT
      run g pk (next p0 out1.1 outT.1) outT.2 live) := by
  rw [run_bind,request_run,PrimeFullFieldSource.ballotFullSimTranscript_factor]
  simp only [Functor.map_map,bind_map_left]
  apply bind_congr
  intro cs1
  rw [run_bind,request_run,PrimeFullFieldSource.ballotFullSimTranscript_factor]
  simp only [Functor.map_map,bind_map_left]

omit [Fact p.Prime] in
theorem continuation_eq (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (rs : ZMod q × ZMod q) (p0 : Proof01 (ZMod q) (PrimeGroup p q)) :
    continuation g pk vote attacker rs p0 = (do
      let p1 ← ballotProofQuery (false,rs.2)
      let pt ← ballotProofQuery (vote,rs.1+rs.2)
      afterAliceProofs g pk vote attacker rs p0 p1 pt) := rfl

/-- Exact specialization to the existing submission continuation. -/
theorem continuation_run (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (rs : ZMod q × ZMod q) (p0 : Proof01 (ZMod q) (PrimeGroup p q))
    (state : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    run g pk (continuation g pk vote attacker rs p0) state live = (do
      let cs1 ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmt1 := honestProofStatement g pk (false,rs.2)
      let tr1 := (ballotSimCommit stmt1 cs1.1 (cs1.2.1,cs1.2.2.1,cs1.2.2.2),
        cs1.1,(cs1.2.1,cs1.2.2.1,cs1.2.2.2))
      let out1 := state.program stmt1 tr1
      let csT ← PrimeFullFieldSource.drawTranscriptScalars q
      let stmtT := honestProofStatement g pk (vote,rs.1+rs.2)
      let trT := (ballotSimCommit stmtT csT.1 (csT.2.1,csT.2.2.1,csT.2.2.2),
        csT.1,(csT.2.1,csT.2.2.1,csT.2.2.2))
      let outT := out1.2.program stmtT trT
      run g pk (afterAliceProofs g pk vote attacker rs p0 out1.1 outT.1) outT.2 live) := by
  rw [continuation_eq]
  exact remaining_program_bind g pk vote rs p0 (afterAliceProofs g pk vote attacker rs) state live

#print axioms remaining_program_bind
#print axioms continuation_eq
#print axioms continuation_run
end ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSource
