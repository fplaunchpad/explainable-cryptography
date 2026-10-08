import ExplainableCrypto.Helios.Computational.ScalarComplementMachine
import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCallerSource
import ExplainableCrypto.Helios.Computational.BitPortTransfer


namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 543
instance : NeZero size := ⟨by decide⟩
def powerLayout : Fin 15 ⊕ Fin 23 ≃ Fin 38 :=
  (Equiv.sumComm _ _).trans finSumFinEquiv
def multiplyLayout : Fin 11 ⊕ Fin 27 ≃ Fin 38 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [23,24,25,26,27,28,29,30,31,32,33,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,34,35,36,37]
    (by decide +kernel) (by decide +kernel))
def transferLabels : BitPortTransfer.Label ≃ Fin 4 where
  toFun | .clear => 0 | .copy false => 1 | .copy true => 2 | .done => 3
  invFun := ![.clear,.copy false,.copy true,.done]
  left_inv l := by cases l with
    | clear => rfl
    | copy b => cases b <;> rfl
    | done => rfl
  right_inv l := by fin_cases l <;> rfl
private def transferTable (which : Fin 9) : List (Fin 38) :=
  ![[12,30,26,0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,29,31,32,33,34,35,36,37],
    [16,34,26,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18,19,20,21,22,23,24,25,27,28,29,30,31,32,33,35,36,37],
    [6,29,26,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,30,31,32,33,34,35,36,37],
    [23,3,26,0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,24,25,27,28,29,30,31,32,33,34,35,36,37],
    [17,34,26,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,19,20,21,22,23,24,25,27,28,29,30,31,32,33,35,36,37],
    [9,36,26,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,29,30,31,32,33,34,35,37],
    [23,31,26,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,24,25,27,28,29,30,32,33,34,35,36,37],
    [3,33,26,0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,29,30,31,32,34,35,36,37],
    [23,3,26,0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,24,25,27,28,29,30,31,32,33,34,35,36,37]] which

def transferLayout (which : Fin 9) : BitCopyMachine.Stack ⊕ Fin 35 ≃ Fin 38 :=
  ((Equiv.sumCongr PrimeNonceCiphertextMachine.copyPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 38 = (transferTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (transferTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def consumes (which : Fin 9) : Bool := which == 3 || which == 6 || which == 7 || which == 8
def transferProgram (which : Fin 9) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 38)) transferLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (transferLayout which) (BitPortTransfer.program (consumes which) l))
def parseLayout : Fin 4 ⊕ Fin 34 ≃ Fin 38 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList [30, 24, 25, 36, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29, 31, 32, 33, 34, 35, 37]
    (by decide +kernel) (by decide +kernel))
def parseProgram (l : Fin 3) := TM2StackFrame.relocate parseLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program l)
def complementLayout : Fin 8 ⊕ Fin 30 ≃ Fin 38 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList [2, 11, 3, 4, 5, 1, 8, 9, 0, 6, 7, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
    (by decide +kernel) (by decide +kernel))
def complementProgram (l : Fin 21) := TM2StackFrame.relocate complementLayout (ScalarComplementMachine.program l)
def powerProgram (l : Fin 192) := TM2StackFrame.relocate powerLayout (BinaryModPower.program l)
def multiplyProgram (l : Fin 86) := TM2StackFrame.relocate multiplyLayout (BinaryModMultiply.program l)
def transferLabel (which : Fin 9) (l : Fin 4) : Fin size := ⟨13+4*which.val+l.val,by have := which.isLt; have := l.isLt; unfold size; omega⟩
def parseLabel (l : Fin 3) : Fin size := ⟨49+l.val,by have := l.isLt; unfold size; omega⟩
def powerLabel (which : Fin 2) (l : Fin 192) : Fin size := ⟨52+192*which.val+l.val,by have := which.isLt; have := l.isLt; unfold size; omega⟩
def multiplyLabel (l : Fin 86) : Fin size := ⟨436+l.val,by have := l.isLt; unfold size; omega⟩
def complementLabel (l : Fin 21) : Fin size := ⟨522+l.val,by have := l.isLt; unfold size; omega⟩
def transferReturn (which : Fin 9) : Fin size :=
  ![parseLabel 0,transferLabel 2 0,powerLabel 0 (BinaryModPower.copyLabel 0 0),
    transferLabel 4 0,transferLabel 5 0,powerLabel 1 (BinaryModPower.copyLabel 0 0),
    transferLabel 7 0,multiplyLabel (BinaryModMultiply.copyLabel 0),6] which

def enter (next : Fin size) : Stmt (fun _ : Fin 38 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
def guard (next : Fin size) : Stmt (fun _ : Fin 38 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2) (enter next) (.load (fun _ => 1) .halt)
def clear (port : Fin 38) (again next : Fin size) : Stmt (fun _ : Fin 38 => Bool) (Fin size) (Fin 3) :=
  .pop port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter next) (.goto (fun _ => again)))
def control (l : Fin 13) : Stmt (fun _ : Fin 38 => Bool) (Fin size) (Fin 3) :=
  ![.branch (fun v => v == 2) (.goto (fun _ => complementLabel 0)) (.load (fun _ => 1) .halt),
    guard (transferLabel 0 0),
    .branch (fun v => v == 2)
      (.peek 30 (fun _ b => BinaryModuloCode.memory b)
        (.branch (fun v => v == 0) (enter (transferLabel 1 0)) (.load (fun _ => 1) .halt)))
      (.load (fun _ => 1) .halt),
    guard (transferLabel 3 0),guard (transferLabel 6 0),guard (transferLabel 8 0),
    clear 29 6 7,clear 33 7 8,clear 34 8 9,clear 36 9 10,
    clear 1 10 11,clear 9 11 12,.load (fun _ => 2) .halt] l

def program (l : Fin size) : Stmt (fun _ : Fin 38 => Bool) (Fin size) (Fin 3) :=
  if h : l.val < 13 then control ⟨l.val,h⟩
  else if h : l.val < 49 then
    let which : Fin 9 := ⟨(l.val-13)/4,by omega⟩
    TM2ReturnLink.redirect (transferLabel which) (transferReturn which)
      (transferProgram which ⟨(l.val-13)%4,by omega⟩)
  else if h : l.val < 52 then TM2ReturnLink.redirect parseLabel 2 (parseProgram ⟨l.val-49,by omega⟩)
  else if h : l.val < 436 then
    let which : Fin 2 := ⟨(l.val-52)/192,by omega⟩
    TM2ReturnLink.redirect (powerLabel which) (if which == 0 then 3 else 4)
      (powerProgram ⟨(l.val-52)%192,by omega⟩)
  else if h : l.val < 522 then TM2ReturnLink.redirect multiplyLabel 5 (multiplyProgram ⟨l.val-436,by omega⟩)
  else TM2ReturnLink.redirect complementLabel 1 (complementProgram ⟨l.val-522,by have := l.isLt; unfold size at this; omega⟩)
def code : Code 38 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 38 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (original : Fin 23 → List Bool) : Fin 38 → List Bool :=
  fun k => if h : k.val < 23 then original ⟨k.val,h⟩ else []
def start (original : Fin 23 → List Bool) : Config := ⟨some 0,2,initialWords original⟩
def result (answer : List Bool) (original : Fin 23 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords original) 3 answer⟩

end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
