import ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondAllCommitCallerSource
import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine
open OracleComp BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run

/-- The original flat hash-key object for p1=(false,r2). -/
def key (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : BallotForkPoint (PrimeGroup p q) :=
  (PrimeSecondCommitSource.statement g pk out,PrimeSecondCommitSource.commitment g pk out cs)

def words (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 70 → List Bool :=
  (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk

/-- Reverse execution order of the eight actual typed key coordinates. -/
def sourceValues (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 8 → Nat :=
  let k := key g pk out cs
  fun i => (primeGroupCoordinate
    (![k.2.2.2,k.2.2.1,k.2.1.2,k.2.1.1,k.1.ciphertext.2,k.1.ciphertext.1,
      k.1.publicKey,k.1.generator] i)).val

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result ((ballotKeyBitCodec p q).encode (key g pk out cs))
    (words slack g pk vote s live out cs)

/-- The complete predecessor supplies the existing serializer's work emptiness. -/
theorem source_work (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (j : Fin 5) :
    localWords (words slack g pk vote s live out cs) ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

theorem source_values (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (i : Fin 8) :
    localWords (words slack g pk vote s live out cs) (PrimeSimKeyMachine.sourcePort i) =
      (sourceValues g pk out cs i).bits := by
  fin_cases i <;> rfl

theorem source_values_bound (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (i : Fin 8) :
    sourceValues g pk out cs i < p := (primeGroupCoordinate _).val_lt

theorem source_width (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (i : Fin 8) :
    (sourceValues g pk out cs i).bits.length ≤ (p-1).size := by
  have h := source_values_bound g pk out cs i
  simpa only [←Nat.size_eq_bits_len] using Nat.size_le_size (show sourceValues g pk out cs i ≤ p-1 by omega)

theorem source_encoding (g pk : PrimeGroup p q) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    PrimeSimKeyMachine.encoded (sourceValues g pk out cs) =
      (ballotKeyBitCodec p q).encode (key g pk out cs) := rfl

/-- Full frame presentation for the fixed map, with the new output initially empty. -/
theorem input_embed (old : Fin 70 → List Bool) :
    BitOracleStackFrame.embed layout (PrimeSimKeyMachine.start (localWords old)) (frame old) =
      start old := by
  have hs (k : Fin 71) :
      (BitOracleStackFrame.embed layout (PrimeSimKeyMachine.start (localWords old)) (frame old)).stk k =
        (start old).stk k := by
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

/-- The original full result retains all seventy earlier words. -/
theorem output_embed (old : Fin 70 → List Bool) (answer : List Bool) :
    BitOracleStackFrame.embed layout (PrimeSimKeyMachine.result answer (localWords old)) (frame old) =
      result answer old := by
  have hs (k : Fin 71) :
      (BitOracleStackFrame.embed layout (PrimeSimKeyMachine.result answer (localWords old)) (frame old)).stk k =
        (result answer old).stk k := by
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
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 70) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ =
      (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk k := by
  have hn : (⟨k.val,by omega⟩ : Fin 71) ≠ 70 := by
    intro h
    have hv := congrArg Fin.val h
    change k.val = 70 at hv
    have hk := k.isLt
    omega
  simp [sourceResult,result,Function.update,hn,initialWords,words]

theorem source_key (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (sourceResult slack g pk vote s live out cs).stk 70 =
      (ballotKeyBitCodec p q).encode (key g pk out cs) := rfl

/-- Execute the unchanged encoder from the actual p1 commitment successor.
Every digit, width and work condition is derived; the exact key uses the original codec. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    ∃ charge ≤ cost p,
      BitOracleMachine.run code (clock p)
        (start (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs,charge) := by
  let old := words slack g pk vote s live out cs
  obtain ⟨charge,hc,he⟩ := PrimeSimKeyMachine.charged p (sourceValues g pk out cs)
    (localWords old) (source_work slack g pk vote s live out cs)
    (source_values slack g pk vote s live out cs) (source_values_bound g pk out cs)
  have hf := BitOracleStackFrame.run layout PrimeSimKeyMachine.code (PrimeSimKeyMachine.clock p)
    (PrimeSimKeyMachine.start (localWords old)) (frame old)
  rw [he,map_pure,←code_frame,input_embed,output_embed,source_encoding] at hf
  exact ⟨charge,hc,hf⟩

/-- Complete query-free serialization, retaining all seventy previous words. -/
theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    Prod.fst <$> BitOracleMachine.run code (clock p)
      (start (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk) =
    pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out cs
  rw [he,map_pure]

#print axioms charged_source
#print axioms execution_source

#print axioms source_work
#print axioms source_values
#print axioms source_values_bound
#print axioms source_width
#print axioms source_encoding
#print axioms input_embed
#print axioms output_embed
#print axioms source_retained
#print axioms source_key
end ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine
