import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineSource
import ExplainableCrypto.Helios.Computational.CacheRequestInputRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
open Turing.TM2 BitOracleMachine
abbrev size := 140

def copyLayout : Fin 3 ⊕ Fin 45 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [14,23,24,0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,20,21,22,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel))
def copyProgram (l : Fin 2) := TM2StackFrame.relocate copyLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program l)
def fieldInput : Fin 11 → Fin 48 := ![23,23,23,23,23,26,26,23,23,26,26]
def fieldOutput : Fin 11 → Fin 48 := ![26,26,26,26,26,23,45,44,26,46,47]
def baseLayout : NatPrefixMachine.Stack ⊕ Fin 44 ≃ Fin 48 :=
  (Equiv.sumCongr PrimeNonceCiphertextMachine.parsePorts (Equiv.refl _)).trans
    (finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [23,24,25,26,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47] (by decide +kernel) (by decide +kernel)))
def fieldLayout (phase : Fin 11) : NatPrefixMachine.Stack ⊕ Fin 44 ≃ Fin 48 :=
  baseLayout.trans ((Equiv.swap 23 (fieldInput phase)).trans
    (Equiv.swap (if fieldInput phase == 26 then 23 else 26) (fieldOutput phase)))
def fieldProgram (phase : Fin 11) (l : Fin 9) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 48)) CacheRequestInput.labels BinaryModuloCode.memory
    (fun k => TM2StackFrame.relocate (fieldLayout phase) (FieldPrefixMachine.program k)) l

def copyLabel (l : Fin 2) : Fin size := ⟨39+l.val,by simp only [size] at *; omega⟩
def fieldLabel (phase : Fin 11) (l : Fin 9) : Fin size := ⟨41+9*phase.val+l.val,by simp only [size] at *; omega⟩
def fieldReturn (phase : Fin 11) : Fin size := ⟨1+phase.val,by simp only [size] at *; omega⟩
private def fail : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
private def enter (next : Fin size) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
private def guard (next : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3)) :=
  Stmt.branch (fun v => v == 2) next fail
private def empty (port : Fin 48) (next : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3)) :=
  Stmt.peek port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) next fail)
private def expect (port : Fin 48) (bit : Bool) (next : Fin size) :
    Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  .pop port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == (if bit then 2 else 1)) (enter next) fail)
private def flagTail (b : Bool) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  empty 46 (.push 46 (fun _ => b) (.load (fun _ => 2) .halt))
private def flagCheck : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  .pop 46 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 2) (flagTail true)
      (.branch (fun v => v == 1) (flagTail false) fail))

def control (l : Fin 17) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then guard (enter (copyLabel 0))
  else if h : l.val < 5 then guard (enter ⟨11+l.val,by simp only [size] at *; omega⟩)
  else if l = 5 then guard (empty 23 (enter 24))
  else if l = 6 then guard (enter (fieldLabel 6 0))
  else if l = 7 then guard (empty 26 (enter 29))
  else if l = 8 then guard (enter (fieldLabel 8 0))
  else if l = 9 then guard (empty 23 (enter 34))
  else if l = 10 then guard (enter (fieldLabel 10 0))
  else if l = 11 then guard (empty 26 (enter 16))
  else if h : l.val < 16 then
    .pop 26 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (enter (fieldLabel ⟨l.val-11,by omega⟩ 0))
        (.goto (fun _ => ⟨l.val,by simp only [size] at *; omega⟩)))
  else flagCheck

def header (l : Fin 22) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  if h : l.val < 7 then
    expect 23 (![true,true,true,false,true,false,true] ⟨l.val,h⟩)
      (if l.val = 6 then fieldLabel 0 0 else ⟨18+l.val,by simp only [size] at *; omega⟩)
  else
    let phase : Fin 3 := ⟨(l.val-7)/5,by omega⟩
    let pos : Fin 5 := ⟨(l.val-7)%5,by omega⟩
    expect (![26,23,26] phase) (![true,true,false,false,true] pos)
      (if pos.val = 4 then fieldLabel (![5,7,9] phase) 0 else ⟨18+l.val,by simp only [size] at *; omega⟩)

def program (l : Fin size) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  if h : l.val < 17 then control ⟨l.val,h⟩
  else if h : l.val < 39 then header ⟨l.val-17,by omega⟩
  else if h : l.val < 41 then
    TM2ReturnLink.redirect copyLabel 17 (copyProgram ⟨l.val-39,by omega⟩)
  else
    let phase : Fin 11 := ⟨(l.val-41)/9,by simp only [size] at *; omega⟩
    let label : Fin 9 := ⟨(l.val-41)%9,by omega⟩
    TM2ReturnLink.redirect (fieldLabel phase) (fieldReturn phase) (fieldProgram phase label)
def code : Code 48 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 48 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 44 → List Bool) : Fin 48 → List Bool :=
  fun k => if h : k.val < 44 then old ⟨k.val,h⟩ else []
def start (old : Fin 44 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def resultWords (old : Fin 44 → List Bool) (shadow live flag history : List Bool) : Fin 48 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (initialWords old) 44 shadow) 45 live) 46 flag) 47 history
def result (old : Fin 44 → List Bool) (shadow live flag history : List Bool) : Config :=
  ⟨none,2,resultWords old shadow live flag history⟩
def input (a b c d shadow live flag history : List Bool) : List Bool :=
  bitFieldsEncode [a,b,c,d,bitFieldsEncode [bitFieldsEncode [shadow,bitFieldsEncode [flag,history]],live]]
def fieldClock (n : Nat) := 3*n.size+7+n*(2*n.size+3)
def clock (N : Nat) := 11*fieldClock N+6*N+41
def cost (N : Nat) := 32*clock N

end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
