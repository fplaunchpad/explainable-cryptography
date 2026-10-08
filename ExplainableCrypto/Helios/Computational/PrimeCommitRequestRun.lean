import ExplainableCrypto.Helios.Computational.PrimeSimKeyCaller
import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineRun
import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachineRun
import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineRun
import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineRun
import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondSource
import ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource

/-! Deterministic commitment/key suffix for one proof request. The statement,
fresh scalars and retained state are canonical inputs; each arithmetic program
and the flat key writer are reused unchanged. -/
namespace ExplainableCrypto.Helios.Computational.PrimeCommitRequest
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

abbrev size := PrimeSimKeyCaller.size
instance : NeZero size := ⟨by decide⟩

def aLayout : Fin 38 ⊕ Fin 10 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def aCode : Code 48 543 3 := BitOracleStackFrame.code aLayout PrimeSimCommitMachine.code
def aLabel (l : Fin 543) : Fin size :=
  ⟨966+l.val,by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

def bLayout : Fin 38 ⊕ Fin 10 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [17,1,2,38,4,5,6,7,8,9,10,11,12,13,14,16,15,0,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def bCode : Code 48 543 3 := BitOracleStackFrame.code bLayout PrimeSimCommitMachine.code
def bLabel (l : Fin 543) : Fin size :=
  ⟨1509+l.val,by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

def differenceLayout : Fin 10 ⊕ Fin 38 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [2,10,11,1,23,24,25,26,27,28,0,3,4,5,6,7,8,9,12,13,14,15,16,17,18,19,20,21,22,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def differenceCode : Code 48 66 3 := BitOracleStackFrame.code differenceLayout ScalarDifferenceMachine.code
def differenceLabel (l : Fin 66) : Fin size :=
  ⟨2052+l.val,by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

def gammaLayout : Fin 40 ⊕ Fin 8 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def gammaCode : Code 48 280 3 := BitOracleStackFrame.code gammaLayout PrimeAdjustedBetaMachine.code
def gammaLabel (l : Fin 280) : Fin size :=
  ⟨2118+l.val,by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

def cLayout : Fin 38 ⊕ Fin 10 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,41,2,40,4,5,6,11,8,9,10,1,7,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3,12,38,39,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def cCode : Code 48 543 3 := BitOracleStackFrame.code cLayout PrimeSimCommitMachine.code
def cLabel (l : Fin 543) : Fin size :=
  ⟨2118+(280+l.val),by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

def dLayout : Fin 38 ⊕ Fin 10 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,41,2,42,4,5,6,11,8,9,10,1,7,13,14,16,15,39,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3,12,17,38,40,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def dCode : Code 48 543 3 := BitOracleStackFrame.code dLayout PrimeSimCommitMachine.code
def dLabel (l : Fin 543) : Fin size :=
  ⟨2118+(823+l.val),by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

def keyLayout : Fin 44 ⊕ Fin 4 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def keyCode : Code 48 169 3 := BitOracleStackFrame.code keyLayout PrimeSimKeyMachine.code
def keyLabel (l : Fin 169) : Fin size :=
  ⟨3484+l.val,by have := l.isLt; change l.val < _ at this; unfold size PrimeSimKeyCaller.size; omega⟩

/-- Reenter the already checked p0 key caller at its first commitment instruction.
The raw-prefix labels remain in the finite code but are not executed here. -/
def outerLayout : Fin 44 ⊕ Fin 4 ≃ Fin 48 := finSumFinEquiv
def code : Code 48 size 3 := BitOracleStackFrame.code outerLayout PrimeSimKeyCaller.code

abbrev Config := BitOracleMachine.Config 48 size 3
def start (words : Fin 48 → List Bool) : Config := ⟨some (aLabel 0),2,words⟩
def clock (p q : Nat) := 4*PrimeSimCommitMachine.clock p q +
  ScalarDifferenceMachine.clock q + PrimeAdjustedBetaMachine.clock p q + PrimeSimKeyMachine.clock p
def cost (p q : Nat) := 4*PrimeSimCommitMachine.cost p q +
  ScalarDifferenceMachine.cost q + PrimeAdjustedBetaMachine.cost p q + PrimeSimKeyMachine.cost p

/-- Canonical request input. Context slots0..5 occupy13/14/18/19/20/21;
slots6..9 hold the surrounding state on44..47. Modulus-minus-one digits on22
are an explicit input whose executed origin belongs to the enclosing caller. -/
def inputWords {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) : Fin 48 → List Bool :=
  ![(primeGroupCoordinate stmt.ciphertext.2).val.bits,[],q.bits,[],[],[],p.bits,
    scalarEncode cs.2.2.2,[],[],scalarEncode cs.1,scalarEncode cs.2.1,scalarEncode cs.2.2.1,
    context 0,context 1,(primeGroupCoordinate stmt.publicKey).val.bits,
    (primeGroupCoordinate stmt.generator).val.bits,(primeGroupCoordinate stmt.ciphertext.1).val.bits,
    context 2,context 3,context 4,context 5,(q-1).bits,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
    context 6,context 7,context 8,context 9]

/-- Complete semantic endpoint of the actual deterministic suffix. -/
def result {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) : Config :=
  let com := ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)
  let w := inputWords stmt cs context
  let w := Function.update w 3 (primeGroupCoordinate com.1.1).val.bits
  let w := Function.update w 38 (primeGroupCoordinate com.1.2).val.bits
  let w := Function.update w 1 (scalarEncode (cs.1-cs.2.1))
  let w := Function.update w 39 (primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val.bits
  let w := Function.update w 40 (primeGroupCoordinate com.2.1).val.bits
  let w := Function.update w 42 (primeGroupCoordinate com.2.2).val.bits
  let w := Function.update w 43 ((ballotKeyBitCodec p q).encode (stmt,com))
  ⟨none,2,w⟩

end ExplainableCrypto.Helios.Computational.PrimeCommitRequest

namespace ExplainableCrypto.Helios.Computational.PrimeCommitRequest
open BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

private theorem a_code (l : Fin 543) : code (aLabel l) =
    BitOracleReturnLink.command aLabel (some (bLabel 0)) (aCode l) := by
  fin_cases l <;> rfl

private theorem b_code (l : Fin 543) : code (bLabel l) =
    BitOracleReturnLink.command bLabel (some (differenceLabel 0)) (bCode l) := by
  fin_cases l <;> rfl

private theorem difference_code (l : Fin 66) : code (differenceLabel l) =
    BitOracleReturnLink.command differenceLabel (some (gammaLabel 0)) (differenceCode l) := by
  fin_cases l <;> rfl

private theorem gamma_code (l : Fin 280) : code (gammaLabel l) =
    BitOracleReturnLink.command gammaLabel (some (cLabel 0)) (gammaCode l) := by
  fin_cases l <;> rfl

private theorem c_code (l : Fin 543) : code (cLabel l) =
    BitOracleReturnLink.command cLabel (some (dLabel 0)) (cCode l) := by
  fin_cases l <;> rfl

private theorem d_code (l : Fin 543) : code (dLabel l) =
    BitOracleReturnLink.command dLabel (some (keyLabel 0)) (dCode l) := by
  fin_cases l <;> rfl

private theorem key_code (l : Fin 169) : code (keyLabel l) =
    BitOracleReturnLink.command keyLabel none (keyCode l) := by
  fin_cases l <;> rfl
end ExplainableCrypto.Helios.Computational.PrimeCommitRequest
namespace ExplainableCrypto.Helios.Computational.PrimeCommitRequest
open OracleComp BitOracleMachine
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

private def phaseWords (phase : Nat) (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) : Fin 48 → List Bool :=
  let com := ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)
  let w := inputWords stmt cs context
  let w := if 1 ≤ phase then Function.update w 3 (primeGroupCoordinate com.1.1).val.bits else w
  let w := if 2 ≤ phase then Function.update w 38 (primeGroupCoordinate com.1.2).val.bits else w
  let w := if 3 ≤ phase then Function.update w 1 (scalarEncode (cs.1-cs.2.1)) else w
  let w := if 4 ≤ phase then Function.update w 39 (primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val.bits else w
  let w := if 5 ≤ phase then Function.update w 40 (primeGroupCoordinate com.2.1).val.bits else w
  let w := if 6 ≤ phase then Function.update w 42 (primeGroupCoordinate com.2.2).val.bits else w
  if 7 ≤ phase then Function.update w 43 ((ballotKeyBitCodec p q).encode (stmt,com)) else w

private def extraFrame {n e : Nat} (L : Fin n ⊕ Fin e ≃ Fin 48)
    (w : Fin 48 → List Bool) : Fin e → List Bool := fun i => w (L (.inr i))
private def commitFrame {e : Nat} (L : Fin 38 ⊕ Fin e ≃ Fin 48)
    (w : Fin 48 → List Bool) : Fin 11 → List Bool :=
  ![w (L (.inl 0)),w (L (.inl 7)),w (L (.inl 10)),w (L (.inl 13)),
    w (L (.inl 14)),w (L (.inl 15)),w (L (.inl 18)),w (L (.inl 19)),
    w (L (.inl 20)),w (L (.inl 21)),w (L (.inl 22))]

private def aOperands (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :=
  PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate stmt.generator).val
    (primeGroupCoordinate stmt.ciphertext.1).val cs.2.1.val cs.2.2.1.val
    (commitFrame aLayout (phaseWords 0 stmt cs context))

private def bOperands (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :=
  PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate stmt.publicKey).val
    (primeGroupCoordinate stmt.ciphertext.2).val cs.2.1.val cs.2.2.1.val
    (commitFrame bLayout (phaseWords 1 stmt cs context))

private def cOperands (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :=
  PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate stmt.generator).val
    (primeGroupCoordinate stmt.ciphertext.1).val (cs.1-cs.2.1).val cs.2.2.2.val
    (commitFrame cLayout (phaseWords 4 stmt cs context))

private def dOperands (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :=
  PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate stmt.publicKey).val
    (primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val (cs.1-cs.2.1).val cs.2.2.2.val
    (commitFrame dLayout (phaseWords 5 stmt cs context))

private def gammaRetained (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) : Fin 20 → List Bool :=
  let w := phaseWords 3 stmt cs context
  ![w 1,w 2,w 3,w 4,w 5,w 7,w 8,w 9,w 10,w 11,w 12,w 13,w 14,w 15,w 17,w 18,w 19,w 20,w 21,w 38]
private def gammaOperands (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :=
  PrimeAdjustedBetaMachine.inputWords p q (primeGroupCoordinate stmt.generator).val
    (primeGroupCoordinate stmt.ciphertext.2).val (gammaRetained stmt cs context)

private theorem a_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed aLayout (PrimeSimCommitMachine.start (aOperands stmt cs context))
      (extraFrame aLayout (phaseWords 0 stmt cs context)) =
    (⟨some 0,2,phaseWords 0 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed aLayout (PrimeSimCommitMachine.start (aOperands stmt cs context))
        (extraFrame aLayout (phaseWords 0 stmt cs context))).stk k =
      phaseWords 0 stmt cs context k := by
    obtain ⟨x,rfl⟩ := aLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem a_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed aLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).1.1).val.bits) (aOperands stmt cs context))
      (extraFrame aLayout (phaseWords 0 stmt cs context)) =
    (⟨none,2,phaseWords 1 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed aLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).1.1).val.bits) (aOperands stmt cs context))
        (extraFrame aLayout (phaseWords 0 stmt cs context))).stk k =
      phaseWords 1 stmt cs context k := by
    obtain ⟨x,rfl⟩ := aLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem b_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed bLayout (PrimeSimCommitMachine.start (bOperands stmt cs context))
      (extraFrame bLayout (phaseWords 1 stmt cs context)) =
    (⟨some 0,2,phaseWords 1 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed bLayout (PrimeSimCommitMachine.start (bOperands stmt cs context))
        (extraFrame bLayout (phaseWords 1 stmt cs context))).stk k =
      phaseWords 1 stmt cs context k := by
    obtain ⟨x,rfl⟩ := bLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem b_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed bLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).1.2).val.bits) (bOperands stmt cs context))
      (extraFrame bLayout (phaseWords 1 stmt cs context)) =
    (⟨none,2,phaseWords 2 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed bLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).1.2).val.bits) (bOperands stmt cs context))
        (extraFrame bLayout (phaseWords 1 stmt cs context))).stk k =
      phaseWords 2 stmt cs context k := by
    obtain ⟨x,rfl⟩ := bLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem c_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed cLayout (PrimeSimCommitMachine.start (cOperands stmt cs context))
      (extraFrame cLayout (phaseWords 4 stmt cs context)) =
    (⟨some 0,2,phaseWords 4 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed cLayout (PrimeSimCommitMachine.start (cOperands stmt cs context))
        (extraFrame cLayout (phaseWords 4 stmt cs context))).stk k =
      phaseWords 4 stmt cs context k := by
    obtain ⟨x,rfl⟩ := cLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem c_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed cLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).2.1).val.bits) (cOperands stmt cs context))
      (extraFrame cLayout (phaseWords 4 stmt cs context)) =
    (⟨none,2,phaseWords 5 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed cLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).2.1).val.bits) (cOperands stmt cs context))
        (extraFrame cLayout (phaseWords 4 stmt cs context))).stk k =
      phaseWords 5 stmt cs context k := by
    obtain ⟨x,rfl⟩ := cLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem d_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed dLayout (PrimeSimCommitMachine.start (dOperands stmt cs context))
      (extraFrame dLayout (phaseWords 5 stmt cs context)) =
    (⟨some 0,2,phaseWords 5 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed dLayout (PrimeSimCommitMachine.start (dOperands stmt cs context))
        (extraFrame dLayout (phaseWords 5 stmt cs context))).stk k =
      phaseWords 5 stmt cs context k := by
    obtain ⟨x,rfl⟩ := dLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem d_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed dLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).2.2).val.bits) (dOperands stmt cs context))
      (extraFrame dLayout (phaseWords 5 stmt cs context)) =
    (⟨none,2,phaseWords 6 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed dLayout (PrimeSimCommitMachine.result ((primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).2.2).val.bits) (dOperands stmt cs context))
        (extraFrame dLayout (phaseWords 5 stmt cs context))).stk k =
      phaseWords 6 stmt cs context k := by
    obtain ⟨x,rfl⟩ := dLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 543 3)) (funext hs)

private theorem gamma_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed gammaLayout (PrimeAdjustedBetaMachine.start (gammaOperands stmt cs context))
      (extraFrame gammaLayout (phaseWords 3 stmt cs context)) =
    (⟨some 0,2,phaseWords 3 stmt cs context⟩ : BitOracleMachine.Config 48 280 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed gammaLayout (PrimeAdjustedBetaMachine.start (gammaOperands stmt cs context))
        (extraFrame gammaLayout (phaseWords 3 stmt cs context))).stk k =
      phaseWords 3 stmt cs context k := by
    obtain ⟨x,rfl⟩ := gammaLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 280 3)) (funext hs)

private theorem gamma_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed gammaLayout (PrimeAdjustedBetaMachine.result ((primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val.bits) (gammaOperands stmt cs context))
      (extraFrame gammaLayout (phaseWords 3 stmt cs context)) =
    (⟨none,2,phaseWords 4 stmt cs context⟩ : BitOracleMachine.Config 48 280 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed gammaLayout (PrimeAdjustedBetaMachine.result ((primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val.bits) (gammaOperands stmt cs context))
        (extraFrame gammaLayout (phaseWords 3 stmt cs context))).stk k =
      phaseWords 4 stmt cs context k := by
    obtain ⟨x,rfl⟩ := gammaLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 280 3)) (funext hs)

private theorem difference_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed differenceLayout (ScalarDifferenceMachine.start q.bits (scalarEncode cs.1) (scalarEncode cs.2.1))
      (extraFrame differenceLayout (phaseWords 2 stmt cs context)) =
    (⟨some 0,2,phaseWords 2 stmt cs context⟩ : BitOracleMachine.Config 48 66 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed differenceLayout (ScalarDifferenceMachine.start q.bits (scalarEncode cs.1) (scalarEncode cs.2.1))
        (extraFrame differenceLayout (phaseWords 2 stmt cs context))).stk k =
      phaseWords 2 stmt cs context k := by
    obtain ⟨x,rfl⟩ := differenceLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 66 3)) (funext hs)

private theorem difference_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed differenceLayout (ScalarDifferenceMachine.result q.bits (scalarEncode cs.1) (scalarEncode cs.2.1) (scalarEncode (cs.1-cs.2.1)))
      (extraFrame differenceLayout (phaseWords 2 stmt cs context)) =
    (⟨none,2,phaseWords 3 stmt cs context⟩ : BitOracleMachine.Config 48 66 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed differenceLayout (ScalarDifferenceMachine.result q.bits (scalarEncode cs.1) (scalarEncode cs.2.1) (scalarEncode (cs.1-cs.2.1)))
        (extraFrame differenceLayout (phaseWords 2 stmt cs context))).stk k =
      phaseWords 3 stmt cs context k := by
    obtain ⟨x,rfl⟩ := differenceLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 66 3)) (funext hs)


private def keyOld (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) : Fin 43 → List Bool :=
  fun i => phaseWords 6 stmt cs context ⟨i.val,by omega⟩
private def keyValues (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Fin 8 → Nat :=
  let com := ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)
  ![(primeGroupCoordinate com.2.2).val,(primeGroupCoordinate com.2.1).val,
    (primeGroupCoordinate com.1.2).val,(primeGroupCoordinate com.1.1).val,
    (primeGroupCoordinate stmt.ciphertext.2).val,(primeGroupCoordinate stmt.ciphertext.1).val,
    (primeGroupCoordinate stmt.publicKey).val,(primeGroupCoordinate stmt.generator).val]
private theorem key_work (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) (j : Fin 5) :
    keyOld stmt cs context ⟨23+j.val,by omega⟩ = [] := by fin_cases j <;> rfl
private theorem key_values (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) (i : Fin 8) :
    keyOld stmt cs context (PrimeSimKeyMachine.sourcePort i) = (keyValues stmt cs i).bits := by
  fin_cases i <;> rfl
private theorem key_encoding (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    PrimeSimKeyMachine.encoded (keyValues stmt cs) =
      (ballotKeyBitCodec p q).encode (stmt,ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)) := rfl

private theorem key_input (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed keyLayout (PrimeSimKeyMachine.start (keyOld stmt cs context))
      (extraFrame keyLayout (phaseWords 6 stmt cs context)) =
    (⟨some 0,2,phaseWords 6 stmt cs context⟩ : BitOracleMachine.Config 48 169 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed keyLayout (PrimeSimKeyMachine.start (keyOld stmt cs context))
        (extraFrame keyLayout (phaseWords 6 stmt cs context))).stk k =
      phaseWords 6 stmt cs context k := by
    obtain ⟨x,rfl⟩ := keyLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨some 0,2,w⟩ : BitOracleMachine.Config 48 169 3)) (funext hs)

private theorem key_output (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    BitOracleStackFrame.embed keyLayout (PrimeSimKeyMachine.result ((ballotKeyBitCodec p q).encode (stmt,ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2))) (keyOld stmt cs context))
      (extraFrame keyLayout (phaseWords 6 stmt cs context)) =
    (⟨none,2,phaseWords 7 stmt cs context⟩ : BitOracleMachine.Config 48 169 3) := by
  have hs (k : Fin 48) :
      (BitOracleStackFrame.embed keyLayout (PrimeSimKeyMachine.result ((ballotKeyBitCodec p q).encode (stmt,ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2))) (keyOld stmt cs context))
        (extraFrame keyLayout (phaseWords 6 stmt cs context))).stk k =
      phaseWords 7 stmt cs context k := by
    obtain ⟨x,rfl⟩ := keyLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  exact congrArg (fun w => (⟨none,2,w⟩ : BitOracleMachine.Config 48 169 3)) (funext hs)

attribute [local irreducible] BitOracleMachine.run

private theorem a_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q,
      BitOracleMachine.run aCode (PrimeSimCommitMachine.clock p q)
        (⟨some 0,2,phaseWords 0 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) =
      pure (⟨none,2,phaseWords 1 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := PrimeSimCommitMachine.charged p q
    (primeGroupCoordinate stmt.generator).val (primeGroupCoordinate stmt.ciphertext.1).val cs.2.1.val cs.2.2.1.val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (commitFrame aLayout (phaseWords 0 stmt cs context))
  have ha : PrimeSimCommitMachine.answer p q (primeGroupCoordinate stmt.generator).val
      (primeGroupCoordinate stmt.ciphertext.1).val cs.2.1.val cs.2.2.1.val =
      (primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).1.1).val :=
    (PrimeSimCommitSource.first_coordinate_value stmt cs.1 cs.2.1 cs.2.2.1 cs.2.2.2).symm
  have hf := BitOracleStackFrame.run aLayout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start (aOperands stmt cs context))
    (extraFrame aLayout (phaseWords 0 stmt cs context))
  change BitOracleMachine.run aCode _ _ = _ at hf
  change BitOracleMachine.run PrimeSimCommitMachine.code _
    (PrimeSimCommitMachine.start (aOperands stmt cs context)) = _ at hr
  rw [hr,map_pure,ha,a_input stmt cs context] at hf
  exact ⟨charge,hc,hf.trans (congrArg
    (fun cfg : BitOracleMachine.Config 48 543 3 =>
      (pure (cfg,charge) : OracleComp spec (BitOracleMachine.Config 48 543 3 × Nat)))
    (a_output stmt cs context))⟩

private theorem b_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q,
      BitOracleMachine.run bCode (PrimeSimCommitMachine.clock p q)
        (⟨some 0,2,phaseWords 1 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) =
      pure (⟨none,2,phaseWords 2 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := PrimeSimCommitMachine.charged p q
    (primeGroupCoordinate stmt.publicKey).val (primeGroupCoordinate stmt.ciphertext.2).val cs.2.1.val cs.2.2.1.val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (commitFrame bLayout (phaseWords 1 stmt cs context))
  have ha : PrimeSimCommitMachine.answer p q (primeGroupCoordinate stmt.publicKey).val
      (primeGroupCoordinate stmt.ciphertext.2).val cs.2.1.val cs.2.2.1.val =
      (primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).1.2).val :=
    (PrimeSimCommitSecondSource.second_coordinate_value stmt cs.1 cs.2.1 cs.2.2.1 cs.2.2.2).symm
  have hf := BitOracleStackFrame.run bLayout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start (bOperands stmt cs context))
    (extraFrame bLayout (phaseWords 1 stmt cs context))
  change BitOracleMachine.run bCode _ _ = _ at hf
  change BitOracleMachine.run PrimeSimCommitMachine.code _
    (PrimeSimCommitMachine.start (bOperands stmt cs context)) = _ at hr
  rw [hr,map_pure,ha,b_input stmt cs context] at hf
  exact ⟨charge,hc,hf.trans (congrArg
    (fun cfg : BitOracleMachine.Config 48 543 3 =>
      (pure (cfg,charge) : OracleComp spec (BitOracleMachine.Config 48 543 3 × Nat)))
    (b_output stmt cs context))⟩

private theorem c_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q,
      BitOracleMachine.run cCode (PrimeSimCommitMachine.clock p q)
        (⟨some 0,2,phaseWords 4 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) =
      pure (⟨none,2,phaseWords 5 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := PrimeSimCommitMachine.charged p q
    (primeGroupCoordinate stmt.generator).val (primeGroupCoordinate stmt.ciphertext.1).val (cs.1-cs.2.1).val cs.2.2.2.val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (commitFrame cLayout (phaseWords 4 stmt cs context))
  have ha : PrimeSimCommitMachine.answer p q (primeGroupCoordinate stmt.generator).val
      (primeGroupCoordinate stmt.ciphertext.1).val (cs.1-cs.2.1).val cs.2.2.2.val =
      (primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).2.1).val :=
    (PrimeSimCommitOneSource.first_coordinate_value stmt cs.1 cs.2.1 cs.2.2.1 cs.2.2.2).symm
  have hf := BitOracleStackFrame.run cLayout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start (cOperands stmt cs context))
    (extraFrame cLayout (phaseWords 4 stmt cs context))
  change BitOracleMachine.run cCode _ _ = _ at hf
  change BitOracleMachine.run PrimeSimCommitMachine.code _
    (PrimeSimCommitMachine.start (cOperands stmt cs context)) = _ at hr
  rw [hr,map_pure,ha,c_input stmt cs context] at hf
  exact ⟨charge,hc,hf.trans (congrArg
    (fun cfg : BitOracleMachine.Config 48 543 3 =>
      (pure (cfg,charge) : OracleComp spec (BitOracleMachine.Config 48 543 3 × Nat)))
    (c_output stmt cs context))⟩

private theorem d_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q,
      BitOracleMachine.run dCode (PrimeSimCommitMachine.clock p q)
        (⟨some 0,2,phaseWords 5 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) =
      pure (⟨none,2,phaseWords 6 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := PrimeSimCommitMachine.charged p q
    (primeGroupCoordinate stmt.publicKey).val (primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val (cs.1-cs.2.1).val cs.2.2.2.val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (commitFrame dLayout (phaseWords 5 stmt cs context))
  have ha : PrimeSimCommitMachine.answer p q (primeGroupCoordinate stmt.publicKey).val
      (primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val (cs.1-cs.2.1).val cs.2.2.2.val =
      (primeGroupCoordinate (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)).2.2).val :=
    (PrimeSimCommitOneSource.second_coordinate_value stmt cs.1 cs.2.1 cs.2.2.1 cs.2.2.2).symm
  have hf := BitOracleStackFrame.run dLayout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start (dOperands stmt cs context))
    (extraFrame dLayout (phaseWords 5 stmt cs context))
  change BitOracleMachine.run dCode _ _ = _ at hf
  change BitOracleMachine.run PrimeSimCommitMachine.code _
    (PrimeSimCommitMachine.start (dOperands stmt cs context)) = _ at hr
  rw [hr,map_pure,ha,d_input stmt cs context] at hf
  exact ⟨charge,hc,hf.trans (congrArg
    (fun cfg : BitOracleMachine.Config 48 543 3 =>
      (pure (cfg,charge) : OracleComp spec (BitOracleMachine.Config 48 543 3 × Nat)))
    (d_output stmt cs context))⟩

private theorem difference_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ ScalarDifferenceMachine.cost q,
      BitOracleMachine.run differenceCode (ScalarDifferenceMachine.clock q)
        (⟨some 0,2,phaseWords 2 stmt cs context⟩ : BitOracleMachine.Config 48 66 3) =
      pure (⟨none,2,phaseWords 3 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := ScalarDifferenceMachine.charged_source cs.1 cs.2.1
  change BitOracleMachine.run ScalarDifferenceMachine.code (ScalarDifferenceMachine.clock q)
    (ScalarDifferenceMachine.start q.bits (scalarEncode cs.1) (scalarEncode cs.2.1)) =
    pure (ScalarDifferenceMachine.result q.bits (scalarEncode cs.1) (scalarEncode cs.2.1)
      (scalarEncode (cs.1-cs.2.1)),charge) at hr
  have hf := BitOracleStackFrame.run differenceLayout ScalarDifferenceMachine.code
    (ScalarDifferenceMachine.clock q)
    (ScalarDifferenceMachine.start q.bits (scalarEncode cs.1) (scalarEncode cs.2.1))
    (extraFrame differenceLayout (phaseWords 2 stmt cs context))
  change BitOracleMachine.run differenceCode _ _ = _ at hf
  rw [hr,map_pure,difference_input stmt cs context,difference_output stmt cs context] at hf
  exact ⟨charge,hc,hf⟩

private theorem gamma_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeAdjustedBetaMachine.cost p q,
      BitOracleMachine.run gammaCode (PrimeAdjustedBetaMachine.clock p q)
        (⟨some 0,2,phaseWords 3 stmt cs context⟩ : BitOracleMachine.Config 48 280 3) =
      pure (⟨none,2,phaseWords 4 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := PrimeAdjustedBetaMachine.charged p q
    (primeGroupCoordinate stmt.generator).val (primeGroupCoordinate stmt.ciphertext.2).val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _) (gammaRetained stmt cs context)
  have ha : PrimeAdjustedBetaMachine.answer p q (primeGroupCoordinate stmt.generator).val
      (primeGroupCoordinate stmt.ciphertext.2).val =
      (primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val :=
    (PrimeSimCommitOneSource.adjusted_beta_value stmt.ciphertext.2 stmt.generator).symm
  have hf := BitOracleStackFrame.run gammaLayout PrimeAdjustedBetaMachine.code
    (PrimeAdjustedBetaMachine.clock p q) (PrimeAdjustedBetaMachine.start (gammaOperands stmt cs context))
    (extraFrame gammaLayout (phaseWords 3 stmt cs context))
  change BitOracleMachine.run gammaCode _ _ = _ at hf
  change BitOracleMachine.run PrimeAdjustedBetaMachine.code _
    (PrimeAdjustedBetaMachine.start (gammaOperands stmt cs context)) = _ at hr
  rw [hr,map_pure,ha,gamma_input stmt cs context] at hf
  exact ⟨charge,hc,hf.trans (congrArg
    (fun cfg : BitOracleMachine.Config 48 280 3 =>
      (pure (cfg,charge) : OracleComp spec (BitOracleMachine.Config 48 280 3 × Nat)))
    (gamma_output stmt cs context))⟩

private theorem key_local (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimKeyMachine.cost p,
      BitOracleMachine.run keyCode (PrimeSimKeyMachine.clock p)
        (⟨some 0,2,phaseWords 6 stmt cs context⟩ : BitOracleMachine.Config 48 169 3) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  have hv (i : Fin 8) : keyValues stmt cs i < p := by
    fin_cases i <;> exact ZMod.val_lt _
  obtain ⟨charge,hc,hr⟩ := PrimeSimKeyMachine.charged p (keyValues stmt cs) (keyOld stmt cs context)
    (key_work stmt cs context) (key_values stmt cs context) hv
  have hf := BitOracleStackFrame.run keyLayout PrimeSimKeyMachine.code
    (PrimeSimKeyMachine.clock p) (PrimeSimKeyMachine.start (keyOld stmt cs context))
    (extraFrame keyLayout (phaseWords 6 stmt cs context))
  change BitOracleMachine.run keyCode _ _ = _ at hf
  rw [hr,map_pure,key_encoding,key_input,key_output] at hf
  exact ⟨charge,hc,hf⟩

private theorem key_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimKeyMachine.cost p,
      BitOracleMachine.run code (PrimeSimKeyMachine.clock p)
        (⟨some (keyLabel 0),2,phaseWords 6 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := key_local stmt cs context
  have h := BitOracleReturnLink.rename_run keyCode code keyLabel key_code
    (PrimeSimKeyMachine.clock p)
    (⟨some 0,2,phaseWords 6 stmt cs context⟩ : BitOracleMachine.Config 48 169 3)
  rw [hr,map_pure] at h
  exact ⟨charge,hc,h⟩

private theorem d_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p),
      BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))
        (⟨some (dLabel 0),2,phaseWords 5 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := d_local stmt cs context
  obtain ⟨lastCharge,hlc,hl⟩ := key_tail stmt cs context
  have hh : ∀ v ∈ support (BitOracleMachine.run dCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 5 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      v.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run dCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 5 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSimKeyMachine.clock p)
        (BitOracleReturnLink.embed dLabel (some (keyLabel 0)) v.1)), last.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeSimKeyMachine.clock p)
      (⟨some (keyLabel 0),2,phaseWords 6 stmt cs context⟩ : Config)), last.1.l = none
    rw [hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run dCode code dLabel (keyLabel 0) d_code
    (PrimeSimCommitMachine.clock p q) (PrimeSimKeyMachine.clock p)
    (⟨some 0,2,phaseWords 5 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) hh ht
  rw [hr,pure_bind] at h
  change BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))
      (⟨some (dLabel 0),2,phaseWords 5 stmt cs context⟩ : Config) =
    (do let last ← BitOracleMachine.run code (PrimeSimKeyMachine.clock p)
          (⟨some (keyLabel 0),2,phaseWords 6 stmt cs context⟩ : Config)
        pure (last.1,charge+last.2)) at h
  rw [hl,pure_bind] at h
  exact ⟨charge+lastCharge,Nat.add_le_add hc hlc,h⟩

private theorem c_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p)),
      BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))
        (⟨some (cLabel 0),2,phaseWords 4 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := c_local stmt cs context
  obtain ⟨lastCharge,hlc,hl⟩ := d_tail stmt cs context
  have hh : ∀ v ∈ support (BitOracleMachine.run cCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 4 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      v.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run cCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 4 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))
        (BitOracleReturnLink.embed cLabel (some (dLabel 0)) v.1)), last.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))
      (⟨some (dLabel 0),2,phaseWords 5 stmt cs context⟩ : Config)), last.1.l = none
    rw [hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run cCode code cLabel (dLabel 0) c_code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))
    (⟨some 0,2,phaseWords 4 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) hh ht
  rw [hr,pure_bind] at h
  change BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))
      (⟨some (cLabel 0),2,phaseWords 4 stmt cs context⟩ : Config) =
    (do let last ← BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))
          (⟨some (dLabel 0),2,phaseWords 5 stmt cs context⟩ : Config)
        pure (last.1,charge+last.2)) at h
  rw [hl,pure_bind] at h
  exact ⟨charge+lastCharge,Nat.add_le_add hc hlc,h⟩

private theorem gamma_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeAdjustedBetaMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p))),
      BitOracleMachine.run code (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))
        (⟨some (gammaLabel 0),2,phaseWords 3 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := gamma_local stmt cs context
  obtain ⟨lastCharge,hlc,hl⟩ := c_tail stmt cs context
  have hh : ∀ v ∈ support (BitOracleMachine.run gammaCode (PrimeAdjustedBetaMachine.clock p q)
      (⟨some 0,2,phaseWords 3 stmt cs context⟩ : BitOracleMachine.Config 48 280 3)),
      v.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run gammaCode (PrimeAdjustedBetaMachine.clock p q)
      (⟨some 0,2,phaseWords 3 stmt cs context⟩ : BitOracleMachine.Config 48 280 3)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))
        (BitOracleReturnLink.embed gammaLabel (some (cLabel 0)) v.1)), last.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))
      (⟨some (cLabel 0),2,phaseWords 4 stmt cs context⟩ : Config)), last.1.l = none
    rw [hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run gammaCode code gammaLabel (cLabel 0) gamma_code
    (PrimeAdjustedBetaMachine.clock p q) (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))
    (⟨some 0,2,phaseWords 3 stmt cs context⟩ : BitOracleMachine.Config 48 280 3) hh ht
  rw [hr,pure_bind] at h
  change BitOracleMachine.run code (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))
      (⟨some (gammaLabel 0),2,phaseWords 3 stmt cs context⟩ : Config) =
    (do let last ← BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))
          (⟨some (cLabel 0),2,phaseWords 4 stmt cs context⟩ : Config)
        pure (last.1,charge+last.2)) at h
  rw [hl,pure_bind] at h
  exact ⟨charge+lastCharge,Nat.add_le_add hc hlc,h⟩

private theorem difference_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ ScalarDifferenceMachine.cost q + (PrimeAdjustedBetaMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p)))),
      BitOracleMachine.run code (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))
        (⟨some (differenceLabel 0),2,phaseWords 2 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := difference_local stmt cs context
  obtain ⟨lastCharge,hlc,hl⟩ := gamma_tail stmt cs context
  have hh : ∀ v ∈ support (BitOracleMachine.run differenceCode (ScalarDifferenceMachine.clock q)
      (⟨some 0,2,phaseWords 2 stmt cs context⟩ : BitOracleMachine.Config 48 66 3)),
      v.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run differenceCode (ScalarDifferenceMachine.clock q)
      (⟨some 0,2,phaseWords 2 stmt cs context⟩ : BitOracleMachine.Config 48 66 3)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))
        (BitOracleReturnLink.embed differenceLabel (some (gammaLabel 0)) v.1)), last.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))
      (⟨some (gammaLabel 0),2,phaseWords 3 stmt cs context⟩ : Config)), last.1.l = none
    rw [hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run differenceCode code differenceLabel (gammaLabel 0) difference_code
    (ScalarDifferenceMachine.clock q) (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))
    (⟨some 0,2,phaseWords 2 stmt cs context⟩ : BitOracleMachine.Config 48 66 3) hh ht
  rw [hr,pure_bind] at h
  change BitOracleMachine.run code (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))
      (⟨some (differenceLabel 0),2,phaseWords 2 stmt cs context⟩ : Config) =
    (do let last ← BitOracleMachine.run code (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))
          (⟨some (gammaLabel 0),2,phaseWords 3 stmt cs context⟩ : Config)
        pure (last.1,charge+last.2)) at h
  rw [hl,pure_bind] at h
  exact ⟨charge+lastCharge,Nat.add_le_add hc hlc,h⟩

private theorem b_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q + (ScalarDifferenceMachine.cost q + (PrimeAdjustedBetaMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p))))),
      BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))))
        (⟨some (bLabel 0),2,phaseWords 1 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := b_local stmt cs context
  obtain ⟨lastCharge,hlc,hl⟩ := difference_tail stmt cs context
  have hh : ∀ v ∈ support (BitOracleMachine.run bCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 1 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      v.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run bCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 1 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      ∀ last ∈ support (BitOracleMachine.run code (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))
        (BitOracleReturnLink.embed bLabel (some (differenceLabel 0)) v.1)), last.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    change ∀ last ∈ support (BitOracleMachine.run code (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))
      (⟨some (differenceLabel 0),2,phaseWords 2 stmt cs context⟩ : Config)), last.1.l = none
    rw [hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run bCode code bLabel (differenceLabel 0) b_code
    (PrimeSimCommitMachine.clock p q) (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))
    (⟨some 0,2,phaseWords 1 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) hh ht
  rw [hr,pure_bind] at h
  change BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))))
      (⟨some (bLabel 0),2,phaseWords 1 stmt cs context⟩ : Config) =
    (do let last ← BitOracleMachine.run code (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))
          (⟨some (differenceLabel 0),2,phaseWords 2 stmt cs context⟩ : Config)
        pure (last.1,charge+last.2)) at h
  rw [hl,pure_bind] at h
  exact ⟨charge+lastCharge,Nat.add_le_add hc hlc,h⟩

private theorem a_tail (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (ScalarDifferenceMachine.cost q + (PrimeAdjustedBetaMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p)))))),
      BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))))
        (⟨some (aLabel 0),2,phaseWords 0 stmt cs context⟩ : Config) =
      pure (⟨none,2,phaseWords 7 stmt cs context⟩,charge) := by
  obtain ⟨charge,hc,hr⟩ := a_local stmt cs context
  obtain ⟨lastCharge,hlc,hl⟩ := b_tail stmt cs context
  have hh : ∀ v ∈ support (BitOracleMachine.run aCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 0 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      v.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    rfl
  have ht : ∀ v ∈ support (BitOracleMachine.run aCode (PrimeSimCommitMachine.clock p q)
      (⟨some 0,2,phaseWords 0 stmt cs context⟩ : BitOracleMachine.Config 48 543 3)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))))
        (BitOracleReturnLink.embed aLabel (some (bLabel 0)) v.1)), last.1.l = none := by
    rw [hr]
    intro v hv
    obtain rfl := eq_of_mem_support_pure _ hv
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))))
      (⟨some (bLabel 0),2,phaseWords 1 stmt cs context⟩ : Config)), last.1.l = none
    rw [hl]
    intro last hlast
    obtain rfl := eq_of_mem_support_pure _ hlast
    rfl
  have h := BitOracleReturnLink.run aCode code aLabel (bLabel 0) a_code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))))
    (⟨some 0,2,phaseWords 0 stmt cs context⟩ : BitOracleMachine.Config 48 543 3) hh ht
  rw [hr,pure_bind] at h
  change BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))))
      (⟨some (aLabel 0),2,phaseWords 0 stmt cs context⟩ : Config) =
    (do let last ← BitOracleMachine.run code (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p))))))
          (⟨some (bLabel 0),2,phaseWords 1 stmt cs context⟩ : Config)
        pure (last.1,charge+last.2)) at h
  rw [hl,pure_bind] at h
  exact ⟨charge+lastCharge,Nat.add_le_add hc hlc,h⟩

/-- Reenter the existing concrete caller at its commitment boundary for an arbitrary
canonical typed statement and transcript. All seven executions, full retained
state and actual instruction charges are derived; the original raw prefix is not
assumed to have executed. -/
theorem charged (stmt : BallotStatement (PrimeGroup p q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (context : Fin 10 → List Bool) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q) (start (inputWords stmt cs context)) =
      pure (result stmt cs context,charge) := by
  have hclock : clock p q = PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (ScalarDifferenceMachine.clock q + (PrimeAdjustedBetaMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimCommitMachine.clock p q + (PrimeSimKeyMachine.clock p)))))) := by unfold clock; omega
  have hcost : cost p q = PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (ScalarDifferenceMachine.cost q + (PrimeAdjustedBetaMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimCommitMachine.cost p q + (PrimeSimKeyMachine.cost p)))))) := by unfold cost; omega
  obtain ⟨charge,hc,hr⟩ := a_tail stmt cs context
  rw [hcost,hclock]
  exact ⟨charge,hc,hr⟩

#print axioms charged

end ExplainableCrypto.Helios.Computational.PrimeCommitRequest
