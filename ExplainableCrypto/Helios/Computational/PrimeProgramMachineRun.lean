import ExplainableCrypto.Helios.Computational.PrimeProgramMachine
import ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgramMachine
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 400000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) : Config :=
  BitOracleReturnLink.embed tailLabel none
    (PrimeProgrammedHistoryMachine.sourceResult slack g pk vote s live out)

/-- Execute preparation, insertion, collision cleanup, nested statement encoding
and history prepend, with every local premise derived from the original source. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    ∃ charge ≤ cost p q raw.length,
      BitOracleMachine.run code (clock p q raw.length)
        (start (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk) =
      pure (sourceResult slack g pk vote s live out,charge) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  obtain ⟨a,ha,hp⟩ := PrimeProgrammedInsertMachine.charged_source slack g pk vote s live out
  obtain ⟨b,hb,ht⟩ := PrimeProgrammedHistoryMachine.charged_source slack g pk vote s live out
  have boundary : BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out) =
      BitOracleReturnLink.embed tailLabel none (PrimeProgrammedHistoryMachine.start
        (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out).stk) := rfl
  have tail : BitOracleMachine.run code (PrimeProgrammedHistoryMachine.clock p raw.length)
      (BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
        (PrimeProgrammedInsertMachine.sourceResult slack g pk vote s live out)) =
      pure (sourceResult slack g pk vote s live out,b) := by
    rw [boundary,BitOracleReturnLink.rename_run _ _ _ tail_code,ht,map_pure]
    rfl
  have hh : ∀ first ∈ support (BitOracleMachine.run PrimeProgrammedInsertMachine.code
      (PrimeProgrammedInsertMachine.clock p q raw.length)
      (PrimeProgrammedInsertMachine.start (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk)),
      first.1.l = none := by
    rw [hp]
    intro first hf
    rw [eq_of_mem_support_pure _ hf]
    rfl
  have hc : ∀ first ∈ support (BitOracleMachine.run PrimeProgrammedInsertMachine.code
      (PrimeProgrammedInsertMachine.clock p q raw.length)
      (PrimeProgrammedInsertMachine.start (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeProgrammedHistoryMachine.clock p raw.length)
        (BitOracleReturnLink.embed prefixLabel (some (tailLabel 0)) first.1)), last.1.l = none := by
    rw [hp]
    intro first hf
    rw [eq_of_mem_support_pure _ hf,tail]
    intro last hl
    rw [eq_of_mem_support_pure _ hl]
    rfl
  refine ⟨a+b,Nat.add_le_add ha hb,?_⟩
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed prefixLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ prefix_code _ _ _ hh hc,hp]
  simp only [pure_bind,tail]

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
    cfg.stk 47 = (ballotStatementBitCodec p q).list.encode next.programmed :=
  PrimeProgrammedHistoryMachine.source_state slack g pk vote s live out

#print axioms charged_source
#print axioms source_state
end ExplainableCrypto.Helios.Computational.PrimeProgramMachine
