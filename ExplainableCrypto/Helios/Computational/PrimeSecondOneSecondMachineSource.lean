import ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondOneFirstMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource
import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondMachine
open OracleComp BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run

def words (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 69 → List Bool :=
  (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result (primeGroupCoordinate (PrimeSecondCommitSource.commitment g pk out cs).2.2).val.bits
    (words slack g pk vote s live out cs)

/-- All prior words survive the new one-branch coordinate. -/
theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 69) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ =
      (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk k := by
  have hn : (⟨k.val,by omega⟩ : Fin 70) ≠ 69 := by
    intro h
    have hv := congrArg Fin.val h
    change k.val = 69 at hv
    have hk := k.isLt
    omega
  simp [sourceResult,result,Function.update,hn,initialWords,words]

theorem source_coordinate (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (sourceResult slack g pk vote s live out cs).stk 69 =
      (primeGroupCoordinate (PrimeSecondCommitSource.commitment g pk out cs).2.2).val.bits := rfl

/-- The complement uses canonical d=c-e; d=0 executes exponent q. -/
theorem answer_source (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    PrimeSimCommitMachine.answer p q (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val
      (cs.1-cs.2.1).val cs.2.2.2.val =
      (primeGroupCoordinate (PrimeSecondCommitSource.commitment g pk out cs).2.2).val := by
  simpa only [PrimeSimCommitMachine.answer,PrimeSecondCommitSource.commitment,
    PrimeSecondCommitSource.statement,honestProofStatement] using
    (PrimeSimCommitOneSource.second_coordinate_value (PrimeSecondCommitSource.statement g pk out)
      cs.1 cs.2.1 cs.2.2.1 cs.2.2.2).symm

theorem source_inputs_embed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let old := words slack g pk vote s live out cs
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val (cs.1-cs.2.1).val cs.2.2.2.val (localFrame old)))
      (frame old) = start old := by
  dsimp only
  have hs (k : Fin 70) :
      (BitOracleStackFrame.embed layout
        (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
          (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val (cs.1-cs.2.1).val cs.2.2.2.val
          (localFrame (words slack g pk vote s live out cs))))
        (frame (words slack g pk vote s live out cs))).stk k =
      (start (words slack g pk vote s live out cs)).stk k := by
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
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val (cs.1-cs.2.1).val cs.2.2.2.val (localFrame old)))
      (frame old) = result answer old := by
  dsimp only
  have hs (k : Fin 70) :
      (BitOracleStackFrame.embed layout
        (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
          (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val (cs.1-cs.2.1).val cs.2.2.2.val
          (localFrame (words slack g pk vote s live out cs))))
        (frame (words slack g pk vote s live out cs))).stk k =
      (result answer (words slack g pk vote s live out cs)).stk k := by
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

/-- Execute the unchanged numeric code from the actual preceding source state.
Canonical operands, frame and charge are derived, not caller certificates. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs,charge) := by
  let old := words slack g pk vote s live out cs
  let operands := PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val
    (cs.1-cs.2.1).val cs.2.2.2.val (localFrame old)
  obtain ⟨charge,hc,hr⟩ := PrimeSimCommitMachine.charged p q (primeGroupCoordinate pk).val (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val
    (cs.1-cs.2.1).val cs.2.2.2.val (Fact.out : p.Prime).two_le
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (localFrame old)
  have hf := BitOracleStackFrame.run layout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start operands) (frame old)
  dsimp only [operands,old] at hf hr
  rw [hr,map_pure,←code_frame,source_inputs_embed,source_outputs_embed,answer_source] at hf
  exact ⟨charge,hc,hf⟩

theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSecondOneFirstMachine.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out cs
  rw [he,map_pure]

#print axioms source_retained
#print axioms source_coordinate
#print axioms answer_source
#print axioms source_inputs_embed
#print axioms source_outputs_embed
#print axioms charged_source
#print axioms execution_source
end ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondMachine
