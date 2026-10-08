import ExplainableCrypto.Helios.Computational.ScalarComplementMachine
import ExplainableCrypto.Helios.Computational.BinaryModAddMachineRun
import ExplainableCrypto.Helios.Computational.CacheRoutineCode

namespace ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
open Turing.TM2

def size : Nat := 66
instance : NeZero size := ⟨by decide⟩
def copyLayout : Bool → Fin 3 ⊕ Fin 7 ≃ Fin 10
  | false => finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [1,5,6,0,2,3,4,7,8,9] (by decide +kernel) (by decide +kernel))
  | true => finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [2,5,6,0,1,3,4,7,8,9] (by decide +kernel) (by decide +kernel))
def copyProgram (which : Bool) (l : Fin 2) := TM2StackFrame.relocate (copyLayout which)
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program l)
def parseLayout : Bool → Fin 4 ⊕ Fin 6 ≃ Fin 10
  | false => finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [5,6,7,9,0,1,2,3,4,8] (by decide +kernel) (by decide +kernel))
  | true => finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [5,6,7,4,0,1,2,3,8,9] (by decide +kernel) (by decide +kernel))
def parseProgram (which : Bool) (l : Fin 3) := TM2StackFrame.relocate (parseLayout which)
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program l)
def differenceLayout : Fin 8 ⊕ Fin 2 ≃ Fin 10 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [9,4,5,6,7,8,0,3,1,2] (by decide +kernel) (by decide +kernel))
def differenceProgram (l : Fin 42) := TM2StackFrame.relocate differenceLayout (BinaryModAddMachine.program l)

def writerPorts : FrameWriteMachine.Stack ≃ Fin 5 :=
  (List.Nodup.getEquivOfForallMemList
    [FrameWriteMachine.input,FrameWriteMachine.carry,FrameWriteMachine.buffer,
      FrameWriteMachine.output,FrameWriteMachine.counter] (by decide +kernel) (by
        intro x
        rcases x with (k|u)
        · cases k <;> simp [FrameWriteMachine.input,FrameWriteMachine.carry,
            FrameWriteMachine.buffer,FrameWriteMachine.output]
        · cases u; simp [FrameWriteMachine.counter])).symm
def writerLayout : Fin 5 ⊕ Fin 5 ≃ Fin 10 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [4,5,6,3,9,0,1,2,7,8] (by decide +kernel) (by decide +kernel))
def writerProgram (l : Fin CacheRoutineCode.writerSize) := TM2StackFrame.relocate writerLayout
  (TM2FiniteCoordinates.program writerPorts CacheRoutineCode.writerLabels
    BinaryModuloCode.memory FrameWriteMachine.program l)
def copyLabel (which : Bool) (l : Fin 2) : Fin size :=
  ⟨6+2*which.toNat+l.val,by cases which <;> simp [size] <;> omega⟩
def parseLabel (which : Bool) (l : Fin 3) : Fin size :=
  ⟨10+3*which.toNat+l.val,by cases which <;> simp [size] <;> omega⟩
def differenceLabel (l : Fin 42) : Fin size := ⟨16+l.val,by unfold size; omega⟩
def writerLabel (l : Fin CacheRoutineCode.writerSize) : Fin size :=
  ⟨58+l.val,by have := l.isLt; change l.val < 8 at this; unfold size; omega⟩
def writerEntry : Fin size := writerLabel (CacheRoutineCode.writerLabels .digits)
private def fail : Stmt (fun _ : Fin 10 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
private def enter (l : Fin size) : Stmt (fun _ : Fin 10 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
private def parsed (next : Fin size) : Stmt (fun _ : Fin 10 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2)
    (.peek 5 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (enter next) fail)) fail

def program (l : Fin size) : Stmt (fun _ : Fin 10 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2) (enter (copyLabel false 0)) fail
  else if l = 1 then parsed (copyLabel true 0)
  else if l = 2 then parsed (differenceLabel (BinaryModAddMachine.subLabel 0 0))
  else if l = 3 then .branch (fun v => v == 2) (enter 4) fail
  else if l = 4 then .pop 4 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter writerEntry) (.goto (fun _ => 4)))
  else if l = 5 then .branch (fun v => v == 2) (.load (fun _ => 2) .halt) fail
  else if h : l.val < 8 then TM2ReturnLink.redirect (copyLabel false) (parseLabel false 0)
    (copyProgram false ⟨l.val-6,by omega⟩)
  else if h : l.val < 10 then TM2ReturnLink.redirect (copyLabel true) (parseLabel true 0)
    (copyProgram true ⟨l.val-8,by omega⟩)
  else if h : l.val < 13 then TM2ReturnLink.redirect (parseLabel false) 1
    (parseProgram false ⟨l.val-10,by omega⟩)
  else if h : l.val < 16 then TM2ReturnLink.redirect (parseLabel true) 2
    (parseProgram true ⟨l.val-13,by omega⟩)
  else if h : l.val < 58 then TM2ReturnLink.redirect differenceLabel 3
    (differenceProgram ⟨l.val-16,by omega⟩)
  else TM2ReturnLink.redirect writerLabel 5
    (writerProgram ⟨l.val-58,by have := l.isLt; unfold size at this; change l.val-58 < 8; omega⟩)
def code : BitOracleMachine.Code 10 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 10 size 3
def tick : Config → Config := TM2ReturnLink.tick program
def start (q c e : List Bool) : Config := ⟨some 0,2,![q,c,e,[],[],[],[],[],[],[]]⟩
def result (q c e answer : List Bool) : Config := ⟨none,2,![q,c,e,answer,[],[],[],[],[],[]]⟩
def clock (q : Nat) : Nat := 18*(q-1).size+26*q.size+47
def cost (q : Nat) : Nat := 32*clock q

end ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
