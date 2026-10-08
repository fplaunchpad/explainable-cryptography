import ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSource
namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSourceControls
open PrimeRemainingProgramSource OracleComp
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def g : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 7) (by decide : (2 : ZMod 7)^3=1))
private def pk : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 7) (by decide : (4 : ZMod 7)^3=1))
private def rs : ZMod 3 × ZMod 3 := (1,2)
private def stmt1 := honestProofStatement g pk (false,rs.2)
private def stmtT := honestProofStatement g pk (true,rs.1+rs.2)
private def zeroCommit : BallotCommitment (PrimeGroup 7 3) := ((0,0),(0,0))
private def zeroTranscript : BallotCommitment (PrimeGroup 7 3) × ZMod 3 × BallotResponse (ZMod 3) :=
  (zeroCommit,0,(0,0,0))
private def state : BallotFiniteProgrammedState (ZMod 3) (PrimeGroup 7 3) :=
  ⟨(∅ : BallotFiniteCache (ZMod 3) (PrimeGroup 7 3)).insert (stmt1,zeroCommit) 0,false,[stmt1]⟩
private def first := state.program stmt1 zeroTranscript
private def second := first.2.program stmtT zeroTranscript
private def zeroProof : Proof01 (ZMod 3) (PrimeGroup 7 3) :=
  ballotTranscriptProof zeroCommit 0 (0,0,0)
private def markedProof : Proof01 (ZMod 3) (PrimeGroup 7 3) :=
  ballotTranscriptProof zeroCommit 1 (0,0,0)

/-- Independent modular arithmetic: rs2=2 while rs1+rs2=0 in ZMod3. -/
theorem exact_remaining_statements :
    ((primeGroupCoordinate stmt1.ciphertext.1).val,(primeGroupCoordinate stmt1.ciphertext.2).val) = (4,2) ∧
    ((primeGroupCoordinate stmtT.ciphertext.1).val,(primeGroupCoordinate stmtT.ciphertext.2).val) = (1,2) := by
  decide +kernel
/-- A nearby operand substitution changes the actual statement. -/
theorem wrong_nonce_distinguished :
    stmt1 ≠ honestProofStatement g pk (false,rs.1) ∧
    stmtT ≠ honestProofStatement g pk (true,rs.1) := by decide +kernel
/-- The zero tuple is in the full-field simulator's domain and yields identities. -/
theorem zero_draw_commitments :
    ballotSimCommit stmt1 (0 : ZMod 3) (0,0,0) = zeroCommit ∧
    ballotSimCommit stmtT (0 : ZMod 3) (0,0,0) = zeroCommit := by decide +kernel
/-- Agreeing occupied programming still flags bad; the following fresh request
retains bad and both prepended history entries, including the duplicate. -/
theorem threaded_successor :
    second.2.cache = state.cache.insert (stmtT,zeroCommit) 0 ∧
    second.2.bad = true ∧ second.2.programmed = [stmtT,stmt1,stmt1] := by
  refine ⟨rfl,?_,?_⟩ <;> decide +kernel
/-- Starting the second request from the stale original state loses the first update. -/
theorem stale_state_distinguished :
    second.2.programmed ≠ (state.program stmtT zeroTranscript).2.programmed ∧
    second.2.bad ≠ (state.program stmtT zeroTranscript).2.bad := by decide +kernel
/-- Alice's arbitrary previously returned proof remains in component zero. -/
theorem first_proof_retained :
    (assembleHonestBallot g pk true rs markedProof first.1 second.1).proof 0 = markedProof ∧
    (assembleHonestBallot g pk true rs markedProof first.1 second.1).proof 0 ≠ zeroProof := by
  constructor
  · rfl
  · intro h
    have hc := congrArg (fun proof : Proof01 (ZMod 3) (PrimeGroup 7 3) => proof.one.challenge) h
    change (1 : ZMod 3) = 0 at hc
    exact (by decide : (1 : ZMod 3) ≠ 0) hc

private def live : BallotFiniteCache (ZMod 3) (PrimeGroup 7 3) :=
  (∅ : BallotFiniteCache (ZMod 3) (PrimeGroup 7 3)).insert (stmtT,zeroCommit) 2
/-- A nonempty live cache is carried through the actual first remaining request;
the source query tree and all full-field transcript choices remain present. -/
theorem occupied_request_keeps_live :
    PrimeFirstProgramSource.run g pk (ballotProofQuery (false,rs.2)) state live =
      (fun t => (state.program stmt1 t,live)) <$>
        ballotFullSimTranscript (F := ZMod 3) stmt1 :=
  PrimeFirstProgramSource.request_run g pk (false,rs.2) state live
/-- Resetting this independently chosen live cache would be observable by lookup. -/
theorem live_reset_distinguished :
    live.lookup (stmtT,zeroCommit) = some 2 ∧
    (∅ : BallotFiniteCache (ZMod 3) (PrimeGroup 7 3)).lookup (stmtT,zeroCommit) = none := by
  decide +kernel
#print axioms occupied_request_keeps_live
#print axioms live_reset_distinguished

#print axioms exact_remaining_statements
#print axioms wrong_nonce_distinguished
#print axioms zero_draw_commitments
#print axioms threaded_successor
#print axioms stale_state_distinguished
#print axioms first_proof_retained
end ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSourceControls
