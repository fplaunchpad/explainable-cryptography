import ExplainableCrypto.Helios.Computational.NatFieldWriterMachine
import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
open Turing.TM2 BitOracleMachine
abbrev size := 130
/-- beta, alpha, pk, g: each pair is built from its final field backward. -/
def sourcePort : Fin 4 → Fin 48 := ![0,17,15,16]
def natBase : Fin 7 ⊕ Fin 41 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0, 28, 23, 24, 25, 26, 27, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) (by decide +kernel))
def natLayout (which : Fin 4) := natBase.trans (Equiv.swap 0 (sourcePort which))
def natProgram (which : Fin 4) (l : Fin 21) :=
  TM2StackFrame.relocate (natLayout which) (NatFieldWriterMachine.program l)
def writerBase : Fin 5 ⊕ Fin 43 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [28, 23, 24, 29, 25, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) (by decide +kernel))
def prependLayout : Fin 5 ⊕ Fin 43 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [29, 23, 24, 47, 25, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46] (by decide +kernel) (by decide +kernel))
def prefixLayout : Fin 5 ⊕ Fin 43 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [23, 24, 25, 47, 28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46] (by decide +kernel) (by decide +kernel))
def writerLayout : Fin 4 → Fin 5 ⊕ Fin 43 ≃ Fin 48 :=
  ![writerBase,writerBase,prependLayout,prefixLayout]
def writerProgram (which : Fin 4) (l : Fin 8) :=
  TM2StackFrame.relocate (writerLayout which)
    (TM2FiniteCoordinates.program ScalarDifferenceMachine.writerPorts
      CacheRoutineCode.writerLabels BinaryModuloCode.memory FrameWriteMachine.program l)
def parseLayout : Fin 4 ⊕ Fin 44 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [47, 23, 24, 28, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46] (by decide +kernel) (by decide +kernel))
def parseProgram (l : Fin 3) := TM2StackFrame.relocate parseLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program l)
def incrementProgram (l : Fin 2) := TM2StackFrame.relocate parseLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
    NatFieldWriterMachine.copyLabels BinaryModuloCode.memory BitIncrementMachine.program l)
def natLabel (which : Fin 4) (l : Fin 21) : Fin size :=
  ⟨9+21*which.val+l.val,by have := which.isLt; have := l.isLt; dsimp [size] at *; omega⟩
def writerLabel (which : Fin 4) (l : Fin 8) : Fin size :=
  ⟨93+8*which.val+l.val,by have := which.isLt; have := l.isLt; dsimp [size] at *; omega⟩
def parseLabel (l : Fin 3) : Fin size := ⟨125+l.val,by dsimp [size]; omega⟩
def incrementLabel (l : Fin 2) : Fin size := ⟨128+l.val,by dsimp [size]; omega⟩
def natReturn : Fin 4 → Fin size := ![natLabel 1 0,1,natLabel 3 0,3]
def writerReturn : Fin 4 → Fin size := ![2,4,7,8]
def fail : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
def enter (l : Fin size) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
def guard (s : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3)) :=
  Stmt.branch (fun v : Fin 3 => v == 2) s fail
/-- Exact U(2), pushed backwards; no host serialization operation. -/
def pairPrefix (port : Fin 48) (next : Fin size) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  ([true,true,false,false,true] : List Bool).foldl
    (fun s b => .push port (fun _ => b) s) (enter next)
def program (l : Fin size) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then guard (.goto (fun _ => natLabel 0 0))
  else if l = 1 then guard (pairPrefix 28 (writerLabel 0 3))
  else if l = 2 then guard (.goto (fun _ => natLabel 2 0))
  else if l = 3 then guard (pairPrefix 28 (writerLabel 1 3))
  else if l = 4 then guard (pairPrefix 29 (parseLabel 0))
  else if l = 5 then guard (enter (incrementLabel 0))
  else if l = 6 then guard (enter (writerLabel 2 3))
  else if l = 7 then guard (enter (writerLabel 3 5))
  else if l = 8 then guard (.load (fun _ => 2) .halt)
  else if h : l.val < 93 then
    TM2ReturnLink.redirect (natLabel ⟨(l.val-9)/21,by omega⟩)
      (natReturn ⟨(l.val-9)/21,by omega⟩)
      (natProgram ⟨(l.val-9)/21,by omega⟩ ⟨(l.val-9)%21,by omega⟩)
  else if h : l.val < 125 then
    TM2ReturnLink.redirect (writerLabel ⟨(l.val-93)/8,by omega⟩)
      (writerReturn ⟨(l.val-93)/8,by omega⟩)
      (writerProgram ⟨(l.val-93)/8,by omega⟩ ⟨(l.val-93)%8,by omega⟩)
  else if h : l.val < 128 then TM2ReturnLink.redirect parseLabel 5
    (parseProgram ⟨l.val-125,by omega⟩)
  else TM2ReturnLink.redirect incrementLabel 6 (incrementProgram ⟨l.val-128,by have := l.isLt; dsimp [size] at *; omega⟩)
def code : Code 48 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 48 size 3
def tick : Config → Config := TM2ReturnLink.tick program
def start (old : Fin 48 → List Bool) : Config := ⟨some 0,2,old⟩
def result (history : List Bool) (old : Fin 48 → List Bool) : Config :=
  ⟨none,2,Function.update old 47 history⟩
def statement (g pk alpha beta : Nat) : List Bool :=
  bitFieldsEncode [bitFieldsEncode [uniformNatEncode g,uniformNatEncode pk],
    bitFieldsEncode [uniformNatEncode alpha,uniformNatEncode beta]]
def pairBound (p : Nat) := bitPairSize (groupRecordBitBound p) (groupRecordBitBound p)
def clock (p H : Nat) := 4*NatFieldWriterMachine.clock (p-1)+
  2*FrameWriteMachine.cost (pairBound p)+FrameWriteMachine.cost (statementRecordBitBound p)+
  5*H.size+3*(H+1).size+17
def cost (p H : Nat) := 32*clock p H
end ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine
