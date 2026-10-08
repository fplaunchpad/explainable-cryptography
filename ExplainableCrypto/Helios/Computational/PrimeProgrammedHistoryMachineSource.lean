import ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachineRun
import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

/-- Exact source successor: insertion has already updated cache/flag; this stage
prepends the original statement to its ordered history. Raw context stays original. -/
def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) : Config :=
  let next := (s.program (PrimeSimKeySource.key g pk vote out).1
    (PrimeProgrammedInsertSource.transcript g pk vote out)).2
  result ((ballotStatementBitCodec p q).list.encode next.programmed)
    (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out).stk

private theorem history_eq (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    (s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)).2.programmed =
      (PrimeSimKeySource.key g pk vote out).1 :: s.programmed := by
  unfold BallotFiniteProgrammedState.program
  split <;> rfl

/-- All operands and the uniform original-raw-length bound come from the actual
post-insertion source result, including the seven restored work words. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    ∃ charge ≤ cost p raw.length,
      BitOracleMachine.run code (clock p raw.length)
        (start (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out).stk) =
      pure (sourceResult slack g pk vote s live out,charge) := by
  dsimp only
  let old := (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out).stk
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  let stmt := (PrimeSimKeySource.key g pk vote out).1
  let elements : Fin 4 → PrimeGroup p q := ![stmt.ciphertext.2,stmt.ciphertext.1,stmt.publicKey,stmt.generator]
  let v : Fin 4 → Nat := fun i => (primeGroupCoordinate (elements i)).val
  let hs := s.programmed.map (ballotStatementBitCodec p q).encode
  have hw (j : Fin 7) : old ⟨23+j.val,by omega⟩ = [] :=
    PrimeProgrammedInsertMachine.source_work slack g pk vote s live out j
  have hv (i : Fin 4) : v i < p := (primeGroupCoordinate (elements i)).val_lt
  have hn (i : Fin 4) : old (sourcePort i) = (v i).bits := by
    fin_cases i <;> rfl
  have hh : old 47 = bitFieldsEncode hs := rfl
  have hN : (old 47).length ≤ raw.length :=
    (PrimeProgrammedInsertSource.source_payload_lengths slack g pk vote s live out).2.2
  have hstmt : statement (v 3) (v 2) (v 1) (v 0) =
      (ballotStatementBitCodec p q).encode stmt := rfl
  obtain ⟨charge,hc,he⟩ := charged_bounded p raw.length v hs old hw hv hn hh hN
  refine ⟨charge,hc,?_⟩
  rw [hstmt] at he
  have hout : result (bitFieldsEncode ((ballotStatementBitCodec p q).encode stmt :: hs)) old =
      sourceResult slack g pk vote s live out := by
    dsimp only [sourceResult]
    rw [history_eq]
    rfl
  rwa [hout] at he

/-- Full cache/flag/history agreement with the original state.program successor;
the live cache is exactly the pre-call one. -/
theorem source_state (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    let next := (s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)).2
    let cfg := sourceResult slack g pk vote s live out
    cfg.stk 44 = (ballotCacheBitCodec p q).encode next.cache ∧
    cfg.stk 46 = [next.bad] ∧
    cfg.stk 45 = (ballotCacheBitCodec p q).encode live ∧
    cfg.stk 47 = (ballotStatementBitCodec p q).list.encode next.programmed := by
  obtain ⟨hc,hb,hl,_⟩ := PrimeProgrammedInsertMachine.source_state slack g pk vote s live out
  exact ⟨hc,hb,hl,rfl⟩

/-- History construction changes no other resident word, including updated
cache/flag, nonces, sampled challenge, full key and original raw context. -/
theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) (k : Fin 48) (hk : k ≠ 47) :
    (sourceResult slack g pk vote s live out).stk k =
      (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out).stk k := by
  simp only [sourceResult,result,Function.update_of_ne hk]

/-- Workspace remains available for the next executed state repacking step. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) (j : Fin 7) :
    (sourceResult slack g pk vote s live out).stk ⟨23+j.val,by omega⟩ = [] := by
  rw [source_retained _ _ _ _ _ _ _ _ (by have := j.isLt; intro h; have := congrArg Fin.val h; dsimp at this; omega)]
  exact PrimeProgrammedInsertMachine.source_work slack g pk vote s live out j

#print axioms charged_source
#print axioms source_state
#print axioms source_retained
#print axioms source_work
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
