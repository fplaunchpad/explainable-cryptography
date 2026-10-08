import ExplainableCrypto.Helios.Computational.PrimeSecondAdjustedMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachineSource
import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineRun
import ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondAdjustedMachine
open OracleComp BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run

def words (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 67 → List Bool :=
  (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk

def retained (old : Fin 67 → List Bool) : Fin 20 → List Bool :=
  ![old 1,old 2,old 3,old 4,old 5,old 7,old 8,old 9,old 10,old 11,
    old 12,old 13,old 14,old 15,old 17,old 18,old 19,old 20,old 21,old 38]

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result ((primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val.bits) (words slack g pk vote s live out cs)

theorem source_inputs_embed (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let old := words slack g pk vote s live out cs
    BitOracleStackFrame.embed layout (PrimeAdjustedBetaMachine.start (PrimeAdjustedBetaMachine.inputWords p q (primeGroupCoordinate g).val (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val (retained old))) (frame old) = start old := by
  dsimp only
  let old := words slack g pk vote s live out cs
  have hs (k : Fin 68) :
      (BitOracleStackFrame.embed layout (PrimeAdjustedBetaMachine.start (PrimeAdjustedBetaMachine.inputWords p q (primeGroupCoordinate g).val (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val (retained old))) (frame old)).stk k = (start old).stk k := by
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
    BitOracleStackFrame.embed layout (PrimeAdjustedBetaMachine.result answer (PrimeAdjustedBetaMachine.inputWords p q (primeGroupCoordinate g).val (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val (retained old))) (frame old) = result answer old := by
  dsimp only
  let old := words slack g pk vote s live out cs
  have hs (k : Fin 68) :
      (BitOracleStackFrame.embed layout (PrimeAdjustedBetaMachine.result answer (PrimeAdjustedBetaMachine.inputWords p q (primeGroupCoordinate g).val (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val (retained old))) (frame old)).stk k = (result answer old).stk k := by
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
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 67) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ = (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk k := by
  have hn : (⟨k.val,by omega⟩ : Fin 68) ≠ 67 := by
    intro h
    have hv := congrArg Fin.val h
    change k.val = 67 at hv
    have hk := k.isLt
    omega
  simp [sourceResult,result,Function.update,hn,initialWords,words]

theorem source_coordinate (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (sourceResult slack g pk vote s live out cs).stk 67 = (primeGroupCoordinate ((PrimeSecondCommitSource.statement g pk out).ciphertext.2-g)).val.bits := rfl

/-- The unchanged inverse-power/product controller consumes beta1 and g from
actual reached ports. Its numeric hypotheses and both frames are derived. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs,charge) := by
  obtain ⟨charge,hc,he⟩ := PrimeAdjustedBetaMachine.charged p q
    (primeGroupCoordinate g).val
    (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _)
    (retained (words slack g pk vote s live out cs))
  have hf := BitOracleStackFrame.run layout PrimeAdjustedBetaMachine.code
    (PrimeAdjustedBetaMachine.clock p q)
    (PrimeAdjustedBetaMachine.start (PrimeAdjustedBetaMachine.inputWords p q
      (primeGroupCoordinate g).val
      (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val
      (retained (words slack g pk vote s live out cs))))
    (frame (words slack g pk vote s live out cs))
  rw [he,map_pure,←code_frame,source_inputs_embed,source_outputs_embed] at hf
  have ha := PrimeSimCommitOneSource.adjusted_beta_value
    (PrimeSecondCommitSource.statement g pk out).ciphertext.2 g
  change _ = PrimeAdjustedBetaMachine.answer p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (PrimeSecondCommitSource.statement g pk out).ciphertext.2).val at ha
  rw [←ha] at hf
  exact ⟨charge,hc,hf⟩

theorem source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSecondDifferenceMachine.sourceResult slack g pk vote s live out cs).stk) =
    pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out cs
  rw [he,map_pure]

#print axioms charged_source
#print axioms source
#print axioms source_inputs_embed
#print axioms source_outputs_embed
#print axioms source_retained
#print axioms source_coordinate
end ExplainableCrypto.Helios.Computational.PrimeSecondAdjustedMachine
