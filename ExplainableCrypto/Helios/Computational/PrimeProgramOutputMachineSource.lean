import ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachineRun
import ExplainableCrypto.Helios.Computational.PrimeProgramProofSource
import ExplainableCrypto.Helios.Computational.PrimeProgramRepackSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
open PrimeProgramProofSource (State Cache Draws)

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) : Config :=
  result ((ballotProofBitCodec p q).encode (PrimeProgramProofSource.proof g pk vote out))
    ((ballotBothCachesBitCodec p q).encode (PrimeProgramRepackSource.nextState g pk vote s out,live))
    (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk

/-- Every operand, source width, updated-state bound and blank temporary comes
from the actual original raw caller. The numeric execution has no extra certificate. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    ∃ charge ≤ cost p q raw.length,
      BitOracleMachine.run code (clock p q raw.length)
        (start (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk) =
      pure (sourceResult slack g pk vote s live out,charge) := by
  dsimp only
  let old := (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  let idx : Fin 4 → Fin 4 := ![1,0,3,2]
  let v : Fin 4 → Nat := fun i =>
    (primeGroupCoordinate (PrimeProgramProofSource.groups g pk vote out (idx i))).val
  have hw (j : Fin 15) : old ⟨23+j.val,by omega⟩ = [] :=
    PrimeProgramProofSource.source_work slack g pk vote s live out j
  have hv (i : Fin 4) : v i < p := PrimeProgramProofSource.group_value_lt g pk vote out (idx i)
  have hn (i : Fin 4) : old (natOldSource i) = (v i).bits := by
    fin_cases i <;> rfl
  have hs (i : Fin 4) : (old (scalarOldSource i)).length ≤ groupRecordBitBound q :=
    PrimeProgramProofSource.source_scalar_length slack g pk vote s live out i
  obtain ⟨hc,_,hf,hh⟩ := PrimeProgramRepackSource.source_lengths slack g pk vote s live out
  have hl : (old 45).length ≤ raw.length :=
    (PrimeProgrammedInsertSource.source_payload_lengths slack g pk vote s live out).2.1
  obtain ⟨charge,hcharge,he⟩ := charged p q raw.length v old hw hv hn hs hc hh hl hf.le
  have hp : proofEncoded v old =
      (ballotProofBitCodec p q).encode (PrimeProgramProofSource.proof g pk vote out) := rfl
  have hr : savedEncoded old = (ballotBothCachesBitCodec p q).encode
      (PrimeProgramRepackSource.nextState g pk vote s out,live) :=
    (PrimeProgramRepackSource.source_shape slack g pk vote s live out).symm
  rw [hp,hr] at he
  exact ⟨charge,hcharge,he⟩

/-- The two appended words are the original source operation's returned proof
and updated both-cache state. All prior48 resident words remain literal. -/
theorem source_outputs (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    let op := s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)
    let cfg := sourceResult slack g pk vote s live out
    cfg.stk 48 = (ballotProofBitCodec p q).encode op.1 ∧
    cfg.stk 49 = (ballotBothCachesBitCodec p q).encode (op.2,live) := by
  dsimp only
  rw [PrimeProgramProofSource.program_return]
  exact ⟨rfl,rfl⟩

theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) (k : Fin 48) :
    (sourceResult slack g pk vote s live out).stk ⟨k.val,by omega⟩ =
      (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk k := by
  fin_cases k <;> rfl

/-- The new saved word cannot be confused with the stale saved payload in raw14. -/
theorem source_saved_changed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    (sourceResult slack g pk vote s live out).stk 49 ≠ PrimeProgrammedStateSource.saved s live :=
  PrimeProgramRepackSource.saved_changed g pk vote s live out

#print axioms charged_source
#print axioms source_outputs
#print axioms source_retained
#print axioms source_saved_changed
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
