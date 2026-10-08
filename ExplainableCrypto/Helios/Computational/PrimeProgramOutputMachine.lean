import ExplainableCrypto.Helios.Computational.NatFieldWriterMachineRun
import ExplainableCrypto.Helios.Computational.BitPairWriterMachine
import ExplainableCrypto.Helios.Computational.BallotStateBitSize
import ExplainableCrypto.Helios.Computational.BallotOutputBitSize

/-! Construct the returned proof and updated saved-state codecs from resident
fields. This code does not reenter the nonce-drawing raw prefix. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
open Turing.TM2 BitOracleMachine
abbrev size := 279

def natSource : Fin 4 → Fin 50 := ![38,3,42,40]
def natDest : Fin 4 → Fin 50 := ![28,28,29,29]
def natLayout0 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [38, 28, 23, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def natLayout1 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [3, 28, 23, 24, 25, 26, 27, 0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def natLayout2 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [42, 29, 23, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def natLayout3 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [40, 29, 23, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def natLayout : Fin 4 → Fin 7 ⊕ Fin 43 ≃ Fin 50 := ![natLayout0,natLayout1,natLayout2,natLayout3]
def pairLayout0 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [11, 12, 30, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def pairLayout1 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [1, 7, 31, 23, 24, 25, 26, 0, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def pairLayout2 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [28, 30, 32, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 29, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def pairLayout3 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [29, 31, 33, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 30, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def pairLayout4 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [32, 33, 48, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 30, 31, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49] (by decide +kernel) (by decide +kernel))
def pairLayout5 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [46, 47, 34, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 48, 49] (by decide +kernel) (by decide +kernel))
def pairLayout6 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [44, 34, 35, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 30, 31, 32, 33, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49] (by decide +kernel) (by decide +kernel))
def pairLayout7 : Fin 7 ⊕ Fin 43 ≃ Fin 50 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [35, 45, 49, 23, 24, 25, 26, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48] (by decide +kernel) (by decide +kernel))
def pairLayout : Fin 8 → Fin 7 ⊕ Fin 43 ≃ Fin 50 := ![pairLayout0,pairLayout1,pairLayout2,pairLayout3,pairLayout4,pairLayout5,pairLayout6,pairLayout7]
def natProgram (i : Fin 4) (l : Fin 21) :=
  TM2StackFrame.relocate (natLayout i) (NatFieldWriterMachine.program l)
def pairProgram (i : Fin 8) (l : Fin 23) :=
  TM2StackFrame.relocate (pairLayout i) (BitPairWriterMachine.program l)
def natLabel (i : Fin 4) (l : Fin 21) : Fin size :=
  ⟨11+21*i.val+l.val,by have := i.isLt; have := l.isLt; dsimp [size]; omega⟩
def pairLabel (i : Fin 8) (l : Fin 23) : Fin size :=
  ⟨95+23*i.val+l.val,by have := i.isLt; have := l.isLt; dsimp [size]; omega⟩
def natReturn : Fin 4 → Fin size := ![natLabel 1 0,0,natLabel 3 0,1]
def pairReturn (i : Fin 8) : Fin size :=
  if h : i.val < 7 then pairLabel ⟨i.val+1,by omega⟩ 0 else 2
def fail : Stmt (fun _ : Fin 50 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
def pairPrefix (port : Fin 50) (next : Fin size) : Stmt (fun _ : Fin 50 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2)
    (([true,true,false,false,true] : List Bool).foldl
      (fun s b => .push port (fun _ => b) s) (.goto (fun _ => next))) fail

def program (l : Fin size) : Stmt (fun _ : Fin 50 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then pairPrefix 28 (natLabel 2 0)
  else if l = 1 then pairPrefix 29 (pairLabel 0 0)
  else if l = 2 then .branch (fun v => v == 2) (.load (fun _ => 0) (.goto (fun _ => 3))) fail
  else if h : l.val < 11 then
    .pop ⟨28+(l.val-3),by omega⟩ (fun _ bit => BinaryModuloCode.memory bit)
      (.branch (fun v => v == 0)
        (if l = 10 then .load (fun _ => 2) .halt
          else .goto (fun _ => ⟨l.val+1,by dsimp [size]; omega⟩))
        (.goto (fun _ => l)))
  else if h : l.val < 95 then
    TM2ReturnLink.redirect (natLabel ⟨(l.val-11)/21,by omega⟩)
      (natReturn ⟨(l.val-11)/21,by omega⟩)
      (natProgram ⟨(l.val-11)/21,by omega⟩ ⟨(l.val-11)%21,by omega⟩)
  else TM2ReturnLink.redirect (pairLabel ⟨(l.val-95)/23,by have := l.isLt; dsimp [size] at *; omega⟩)
    (pairReturn ⟨(l.val-95)/23,by have := l.isLt; dsimp [size] at *; omega⟩)
    (pairProgram ⟨(l.val-95)/23,by have := l.isLt; dsimp [size] at *; omega⟩ ⟨(l.val-95)%23,by omega⟩)
def code : Code 50 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 50 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 48 → List Bool) : Fin 50 → List Bool :=
  fun k => if h : k.val < 48 then old ⟨k.val,h⟩ else []
def start (old : Fin 48 → List Bool) : Config := ⟨some (natLabel 0 0),2,initialWords old⟩
def result (proof saved : List Bool) (old : Fin 48 → List Bool) : Config :=
  ⟨none,2,Function.update (Function.update (initialWords old) 48 proof) 49 saved⟩

def groupPairBound (p : Nat) := bitPairSize (groupRecordBitBound p) (groupRecordBitBound p)
def scalarPairBound (q : Nat) := bitPairSize (groupRecordBitBound q) (groupRecordBitBound q)
def branchBound (p q : Nat) := bitPairSize (groupPairBound p) (scalarPairBound q)
def shadowBound (p q N : Nat) := cacheRecordBitBound p q (N+1)
def historyBound (p N : Nat) := bitListSize (statementRecordBitBound p) (N+1)
def flagHistoryBound (p N : Nat) := bitPairSize 1 (historyBound p N)
def programmedBound (p q N : Nat) := bitPairSize (shadowBound p q N) (flagHistoryBound p N)
def pairLeftBounds (p q N : Nat) : Fin 8 → Nat :=
  ![groupRecordBitBound q,groupRecordBitBound q,groupPairBound p,groupPairBound p,
    branchBound p q,1,shadowBound p q N,programmedBound p q N]
def pairRightBounds (p q N : Nat) : Fin 8 → Nat :=
  ![groupRecordBitBound q,groupRecordBitBound q,scalarPairBound q,scalarPairBound q,
    branchBound p q,historyBound p N,flagHistoryBound p N,N]
def tempBounds (p q N : Nat) : Fin 8 → Nat :=
  ![groupPairBound p,groupPairBound p,scalarPairBound q,scalarPairBound q,
    branchBound p q,branchBound p q,flagHistoryBound p N,programmedBound p q N]
def clock (p q N : Nat) := 4*NatFieldWriterMachine.clock (p-1)+
  (∑ i : Fin 8, BitPairWriterMachine.clock (pairLeftBounds p q N i) (pairRightBounds p q N i))+
  (∑ i : Fin 8, tempBounds p q N i)+11
def cost (p q N : Nat) := 32*clock p q N
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
