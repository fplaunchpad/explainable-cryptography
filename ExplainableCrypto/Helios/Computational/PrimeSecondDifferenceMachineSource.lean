import ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondCommitBMachineSource
import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachine
open OracleComp BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run

def words (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 66 → List Bool :=
  (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result (uniformNatEncode (cs.1-cs.2.1).val) (words slack g pk vote s live out cs)

theorem source_inputs_embed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let old := words slack g pk vote s live out cs
    BitOracleStackFrame.embed layout (ScalarDifferenceMachine.start q.bits (uniformNatEncode cs.1.val) (uniformNatEncode cs.2.1.val)) (frame old) = start old := by
  dsimp only
  let old := words slack g pk vote s live out cs
  have hs (k : Fin 67) :
      (BitOracleStackFrame.embed layout (ScalarDifferenceMachine.start q.bits (uniformNatEncode cs.1.val) (uniformNatEncode cs.2.1.val)) (frame old)).stk k = (start old).stk k := by
    obtain ⟨x,rfl⟩ := layout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : Config)) (funext hs)

theorem source_outputs_embed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (answer : List Bool) :
    let old := words slack g pk vote s live out cs
    BitOracleStackFrame.embed layout (ScalarDifferenceMachine.result q.bits (uniformNatEncode cs.1.val) (uniformNatEncode cs.2.1.val) answer) (frame old) = result answer old := by
  dsimp only
  let old := words slack g pk vote s live out cs
  have hs (k : Fin 67) :
      (BitOracleStackFrame.embed layout (ScalarDifferenceMachine.result q.bits (uniformNatEncode cs.1.val) (uniformNatEncode cs.2.1.val) answer) (frame old)).stk k = (result answer old).stk k := by
    obtain ⟨x,rfl⟩ := layout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : Config)) (funext hs)

theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 66) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ = (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk k := by
  have hn : (⟨k.val,by omega⟩ : Fin 67) ≠ 66 := by
    intro h
    have hv := congrArg Fin.val h
    change k.val = 66 at hv
    have hk := k.isLt
    omega
  simp [sourceResult,result,Function.update,hn,initialWords,words]

theorem source_coordinate (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (sourceResult slack g pk vote s live out cs).stk 66 = uniformNatEncode (cs.1-cs.2.1).val := rfl

/-- Actual canonical subtraction executes on the reached p1 scalar words.
All input origins, workspace and retained frames are derived above. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    ∃ charge ≤ cost q,
      BitOracleMachine.run code (clock q)
        (start (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨charge,hc,he⟩ := ScalarDifferenceMachine.charged_source cs.1 cs.2.1
  have hf := BitOracleStackFrame.run layout ScalarDifferenceMachine.code
    (ScalarDifferenceMachine.clock q)
    (ScalarDifferenceMachine.start q.bits (uniformNatEncode cs.1.val)
      (uniformNatEncode cs.2.1.val))
    (frame (words slack g pk vote s live out cs))
  rw [he,map_pure,←code_frame,source_inputs_embed,source_outputs_embed] at hf
  exact ⟨charge,hc,hf⟩

theorem source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    Prod.fst <$> BitOracleMachine.run code (clock q)
      (start (PrimeSecondCommitBMachine.sourceResult slack g pk vote s live out cs).stk) =
    pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out cs
  rw [he,map_pure]

#print axioms charged_source
#print axioms source
#print axioms source_inputs_embed
#print axioms source_outputs_embed
#print axioms source_retained
#print axioms source_coordinate
end ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachine
