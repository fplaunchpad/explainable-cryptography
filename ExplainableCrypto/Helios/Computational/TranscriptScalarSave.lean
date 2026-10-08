import ExplainableCrypto.Helios.Computational.BitPortTransfer
import ExplainableCrypto.Helios.Computational.TM2FiniteCoordinates
import ExplainableCrypto.Helios.Computational.CacheCallerMachineRun

namespace ExplainableCrypto.Helios.Computational.TranscriptScalarSave
open Turing.TM2 OracleComp BitOracleMachine
private def ports : BitCopyMachine.Stack ≃ Fin 3 where
  toFun | .source => 0 | .destination => 1 | .scratch => 2
  invFun k := if k = 0 then .source else if k = 1 then .destination else .scratch
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
private def labels : BitPortTransfer.Label ≃ Fin 4 where
  toFun | .clear => 0 | .copy false => 1 | .copy true => 2 | .done => 3
  invFun k := if k = 0 then .clear else if k = 1 then .copy false else if k = 2 then .copy true else .done
  left_inv k := by cases k with
    | clear => rfl
    | copy b => cases b <;> rfl
    | done => rfl
  right_inv k := by fin_cases k <;> rfl
private def table (j : Fin 3) : List (Fin 23) :=
  ![[7,10,1,0,2,3,4,5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22],
    [7,11,1,0,2,3,4,5,6,8,9,10,12,13,14,15,16,17,18,19,20,21,22],
    [7,12,1,0,2,3,4,5,6,8,9,10,11,13,14,15,16,17,18,19,20,21,22]] j

def layout (j : Fin 3) : BitCopyMachine.Stack ⊕ Fin 20 ≃ Fin 23 :=
  ((Equiv.sumCongr ports (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 23 = (table j).length by fin_cases j <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (table j)
        (by fin_cases j <;> decide +kernel) (by fin_cases j <;> decide +kernel)))
def transferProgram (j : Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 23)) labels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (layout j) (BitPortTransfer.program true l))
def transferState (j : Fin 3) (phase : Option BitPortTransfer.Label)
    (word old : List Bool) (frame : Fin 20 → List Bool) : BitOracleMachine.Config 23 4 3 :=
  TM2FiniteCoordinates.present (Equiv.refl _) labels BinaryModuloCode.memory
    (TM2StackFrame.embed (layout j) (BitPortTransfer.config phase word old []) frame)

def transferLabel (l : Fin 4) : Fin 7 := ⟨2+l.val,by omega⟩
def program (j : Fin 3) (l : Fin 7) : Stmt (fun _ : Fin 23 => Bool) (Fin 7) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2)
    (.goto (fun _ => 1)) (.load (fun _ => 1) .halt)
  else if l = 1 then .pop 2 (fun _ b => CoinWordLoader.encode b)
    (.branch (fun v => v == 0) (.goto (fun _ => transferLabel 0)) (.goto (fun _ => 1)))
  else if h : l.val < 6 then
    BitOracleReturnLink.stmt transferLabel (some 6) (transferProgram j ⟨l.val-2,by omega⟩)
  else .load (fun _ => 2) .halt

def code (j : Fin 3) : Code 23 7 3 := fun l => .compute (program j l)
abbrev Config := BitOracleMachine.Config 23 7 3
/-- The destination and scratch are empty, and the old sampler modulus is on2. -/
def start (j : Fin 3) (word modulus : List Bool) (frame : Fin 20 → List Bool) : Config :=
  ⟨some 0,2,Function.update (transferState j (some .clear) word [] frame).stk 2 modulus⟩
def result (j : Fin 3) (word : List Bool) (frame : Fin 20 → List Bool) : Config :=
  ⟨none,2,Function.update (transferState j none [] word frame).stk 2 []⟩
def clock (word modulus : List Bool) : Nat := 3*word.length+modulus.length+7
def cost (word modulus : List Bool) : Nat := 5*clock word modulus
end ExplainableCrypto.Helios.Computational.TranscriptScalarSave
