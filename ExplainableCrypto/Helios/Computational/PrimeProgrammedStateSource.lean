import ExplainableCrypto.Helios.Computational.PrimeSimKeyCallerSource
import ExplainableCrypto.Helios.Computational.BallotStateCodec
import ExplainableCrypto.Helios.Computational.PrimeFirstProgramSource

/-! Presentation of the typed state at the existing simulator-key boundary.
This derives the saved-field grammar and reusable work from the actual result.
It does not assert that an enclosing finite machine serialized its typed state. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateSource
open OracleComp OracleSpec
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

abbrev State := BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)
abbrev Cache := BallotFiniteCache (ZMod q) (PrimeGroup p q)

def saved (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) : List Bool :=
  (ballotBothCachesBitCodec p q).encode (s,live)

def shadow (s : State (p:=p) (q:=q)) : List Bool :=
  (ballotCacheBitCodec p q).encode s.cache

def history (s : State (p:=p) (q:=q)) : List Bool :=
  (ballotStatementBitCodec p q).list.encode s.programmed

/-- Exact nested shape, retaining ordered repeated statements and both caches. -/
theorem saved_shape (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    saved s live = bitFieldsEncode [bitFieldsEncode
      [shadow s,bitFieldsEncode [[s.bad],history s]],
      (ballotCacheBitCodec p q).encode live] := rfl

/-- The canonical saved record is the actual fifth raw field. -/
theorem raw_shape (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    PrimeHonestInputMachine.input g pk slack vote (saved s live) =
      bitFieldsEncode [uniformNatEncode p,
        (ballotCiphertextBitCodec p q).encode (g,pk),SamplerOperands.input slack q [],
        [vote],bitFieldsEncode [bitFieldsEncode
          [shadow s,bitFieldsEncode [[s.bad],history s]],
          (ballotCacheBitCodec p q).encode live]] := rfl

/-- Canonical raw context survives every actual prefix stage including key output. -/
theorem source_context (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (PrimeSimKeyCaller.sourceResult slack g pk vote (saved s live) out).stk 14 =
      PrimeHonestInputMachine.input g pk slack vote (saved s live) := rfl

/-- Parser work is derived from the reached constructor result. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (j : Fin 5) :
    (PrimeSimKeyCaller.sourceResult slack g pk vote (saved s live) out).stk
      ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

/-- The original complete submission uses exactly the joint draw tuple that
feeds the executed key/state prefix. The remaining source continuation and the
actual state transition are retained; this law asserts no execution of them. -/
theorem submission_draw_source (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    PrimeFirstProgramSource.run g pk (repairedSubmissionPrimeOracle g pk vote attacker) s live = (do
      let draws ← PrimeHonestTranscriptCaller.drawSource q
      let key := PrimeSimKeySource.key g pk vote draws
      let next := s.program key.1
        (key.2,draws.2.1,(draws.2.2.1,draws.2.2.2.1,draws.2.2.2.2))
      PrimeFirstProgramSource.run g pk
        (PrimeFirstProgramSource.continuation g pk vote attacker draws.1 next.1) next.2 live) := by
  rw [PrimeFirstProgramSource.submission_run]
  simp only [PrimeHonestTranscriptCaller.drawSource,bind_assoc,
    pure_bind,PrimeSimKeySource.key]

#print axioms submission_draw_source
#print axioms saved_shape
#print axioms raw_shape
#print axioms source_context
#print axioms source_work
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateSource
