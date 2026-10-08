import ExplainableCrypto.Helios.Computational.PrimeSecondCommitSource
import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachine
open OracleComp BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result (primeGroupCoordinate (PrimeSecondCommitSource.commitment g pk out cs).1.1).val.bits
    (PrimeSecondCommitSource.words slack g pk vote s live out cs)

/-- All earlier words, including the first proof and updated saved state, remain
literal at the second proof's first commitment boundary. -/
theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 59) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ =
      PrimeSecondCommitSource.words slack g pk vote s live out cs k := by
  have hn : (⟨k.val,by omega⟩ : Fin 65) ≠ 60 := by
    intro h
    have hv := congrArg Fin.val h
    change k.val = 60 at hv
    have hk := k.isLt
    omega
  simp [sourceResult,result,Function.update,hn,initialWords]

theorem source_coordinate (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (sourceResult slack g pk vote s live out cs).stk 60 =
      (primeGroupCoordinate (PrimeSecondCommitSource.commitment g pk out cs).1.1).val.bits := rfl

/-- The reached second-proof operands instantiate the existing numeric run.
Its exact charge survives the fixed frame; every bound and presentation premise
is derived from the actual source result, including zero challenge/response. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSecondCommitSource.words slack g pk vote s live out cs)) =
      pure (sourceResult slack g pk vote s live out cs,charge) := by
  let old := PrimeSecondCommitSource.words slack g pk vote s live out cs
  let operands := PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.1).val
    cs.2.1.val cs.2.2.1.val (localFrame old)
  obtain ⟨hp,hg,ha,he,hz⟩ := PrimeSecondCommitSource.source_bounds g pk out cs
  obtain ⟨charge,hc,hr⟩ := PrimeSimCommitMachine.charged p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.1).val
    cs.2.1.val cs.2.2.1.val hp hg ha he hz (localFrame old)
  have hf := BitOracleStackFrame.run layout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start operands) (frame old)
  dsimp only [operands,old] at hf hr
  rw [hr,map_pure,←code_frame,PrimeSecondCommitSource.source_inputs_embed,
    PrimeSecondCommitSource.source_outputs_embed,PrimeSecondCommitSource.answer_source] at hf
  exact ⟨charge,hc,hf⟩

/-- Complete query-free local execution of p1's first commitment. -/
theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSecondCommitSource.words slack g pk vote s live out cs)) =
      pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out cs
  rw [he,map_pure]

#print axioms charged_source
#print axioms execution_source
#print axioms source_retained
#print axioms source_coordinate
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachine
