import ExplainableCrypto.Helios.Computational.CacheInsertOccupiedRun
import ExplainableCrypto.Helios.Computational.TM2TapeRuns

namespace ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine
open Turing.TM2 BitOracleMachine
abbrev size := 5+CacheRoutineCode.insertSize

def insertLabel (l : Fin CacheRoutineCode.insertSize) : Fin size := ⟨5+l.val,by change 5+l.val < 5+CacheRoutineCode.insertSize; omega⟩
def insertEntry : Fin size := insertLabel (CacheRoutineCode.insertLabels (.lookup (.copy false)))
private def fail : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
private def enter (next : Fin size) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
private def flagTail (b : Bool) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .peek 6 (fun _ bit => BinaryModuloCode.memory bit)
    (.branch (fun v => v == 0) (.push 6 (fun _ => b) (enter 2)) fail)
private def capture (collision : Bool) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .pop 6 (fun _ bit => BinaryModuloCode.memory bit)
    (.branch (fun v => v == 2) (flagTail true)
      (.branch (fun v => v == 1) (flagTail collision) fail))
def control (l : Fin 5) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2) (enter insertEntry) fail
  else if l = 1 then .branch (fun v => v == 1) (capture true)
    (.branch (fun v => v == 2) (capture false) fail)
  else .pop (![0,4,5] ⟨l.val-2,by omega⟩) (fun _ bit => BinaryModuloCode.memory bit)
    (.branch (fun v => v == 0)
      (if l = 4 then .load (fun _ => 2) .halt else enter ⟨l.val+1,by have := Nat.pos_of_neZero CacheRoutineCode.insertSize; unfold size; omega⟩)
      (.goto (fun _ => ⟨l.val,by have := Nat.pos_of_neZero CacheRoutineCode.insertSize; unfold size; omega⟩)))
def program (l : Fin size) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  if h : l.val < 5 then control ⟨l.val,h⟩ else
    TM2ReturnLink.redirect insertLabel 1 (CacheRoutineCode.insertCode ⟨l.val-5,by unfold size at *; omega⟩)
def code : Code 12 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 12 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (cache proposed key live history : List Bool) (bad : Bool) : Config :=
  ⟨some 0,2,![cache,[],[],[],[],[],[bad],proposed,key,[],live,history]⟩
def result (cache proposed key live history : List Bool) (bad : Bool) : Config :=
  ⟨none,2,![[],[],[],[],[],[],[bad],proposed,key,cache,live,history]⟩
/-- A bit-length upper bound on the actual initialized input height. -/
def inputBound (cache proposed key live history : List Bool) :=
  1+cache.length+proposed.length+key.length+live.length+history.length
def space (insertFuel inputHeight : Nat) :=
  inputHeight+insertFuel*TM2TapeRuns.codeAccesses CacheRoutineCode.insertCode
def clock (insertFuel inputHeight : Nat) := insertFuel+3*space insertFuel inputHeight+5
def cost (insertFuel inputHeight : Nat) := 32*clock insertFuel inputHeight

end ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine
