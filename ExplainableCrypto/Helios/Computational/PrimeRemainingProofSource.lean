import ExplainableCrypto.Helios.Computational.PrimeRemainingProofRequests
import ExplainableCrypto.Helios.Computational.PrimeRemainingProgramSource

/-! Original two-request source specialized to the returned proof triple and
current state. This stops before `afterAliceProofs`; it does not execute that
continuation or introduce another request implementation. -/
namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProofSource
open OracleComp OracleSpec
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxHeartbeats 600000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

def firstProof (g pk : PrimeGroup p q) (vote : Bool) (s : State (p:=p) (q:=q))
    (out : Draws (q:=q)) : Proof01 (ZMod q) (PrimeGroup p q) :=
  (s.program (PrimeSimKeySource.key g pk vote out).1
    (PrimeProgrammedInsertSource.transcript g pk vote out)).1

/-- The original operations in source order, including their actual successor
state. The first proof and state come from the already completed p0 request. -/
def returned (g pk : PrimeGroup p q) (vote : Bool) (s : State (p:=p) (q:=q))
    (out : Draws (q:=q)) (cs1 csT : PrimeRemainingProofRequests.Scalars (q:=q)) :=
  let stmt1 := honestProofStatement g pk (false,out.1.2)
  let op1 := (PrimeRemainingProofRequests.firstState g pk vote s out).program stmt1 (PrimeProofRequest.transcript stmt1 cs1)
  let stmtT := honestProofStatement g pk (vote,out.1.1+out.1.2)
  let opT := (PrimeRemainingProofRequests.secondState g pk vote s out cs1).program stmtT (PrimeProofRequest.transcript stmtT csT)
  ((firstProof g pk vote s out,op1.1,opT.1),opT.2)

/-- Exact original query semantics with the continuation specialized to return
all three proofs. Both requests draw fresh full-field transcripts; the separate
live cache is returned unchanged by these programming operations. -/
theorem source_run (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    PrimeFirstProgramSource.run g pk (do
      let p1 ← ballotProofQuery (false,out.1.2)
      let pt ← ballotProofQuery (vote,out.1.1+out.1.2)
      pure (firstProof g pk vote s out,p1,pt)) (PrimeRemainingProofRequests.firstState g pk vote s out) live = (do
      let cs1 ← PrimeFullFieldSource.drawTranscriptScalars q
      let csT ← PrimeFullFieldSource.drawTranscriptScalars q
      pure (returned g pk vote s out cs1 csT,live)) := by
  rw [PrimeRemainingProgramSource.remaining_program_bind g pk vote out.1
    (firstProof g pk vote s out) (fun p0 p1 pt => pure (p0,p1,pt))]
  apply bind_congr
  intro cs1
  apply bind_congr
  intro csT
  simp only [PrimeFirstProgramSource.run,runBallotFiniteCache,simulateQ_pure]
  rfl

/-- The final resident endpoint contains precisely the proofs and saved current
state returned by `source_run`, using the original codecs. -/
theorem endpoint_outputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs1 csT : PrimeRemainingProofRequests.Scalars (q:=q)) :
    let ret := returned g pk vote s out cs1 csT
    let w := (PrimeRemainingProofRequests.totalResult slack g pk vote s live out cs1 csT).stk
    w 48 = (ballotProofBitCodec p q).encode ret.1.1 ∧
    w 52 = (ballotProofBitCodec p q).encode ret.1.2.1 ∧
    w 53 = (ballotProofBitCodec p q).encode ret.1.2.2 ∧
    w 49 = (ballotBothCachesBitCodec p q).encode (ret.2,live) := by
  dsimp only
  have h0 := (PrimeProgramOutputCaller.source_outputs slack g pk vote s live out).1
  have h1 := (PrimeRemainingProofRequests.p1_outputs slack g pk vote s live out cs1).1
  have ht := PrimeRemainingProofRequests.total_outputs slack g pk vote s live out cs1 csT
  have hr0 := PrimeRemainingProofRequests.original_retained slack g pk vote s live out cs1 csT 5
  have hr1 := PrimeRemainingProofRequests.p1_retained slack g pk vote s live out cs1 csT 2
  refine ⟨?_,?_,ht.1,ht.2⟩
  · exact hr0.trans h0
  · exact hr1.trans h1

#print axioms source_run
#print axioms endpoint_outputs
end ExplainableCrypto.Helios.Computational.PrimeRemainingProofSource
