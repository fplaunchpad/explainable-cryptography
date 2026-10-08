import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
import ExplainableCrypto.Helios.Computational.BinaryModAddMachine
import ExplainableCrypto.Helios.Computational.ScalarCodec


namespace ExplainableCrypto.Helios.Computational.ScalarComplementMachine
open Turing.TM2

def copyLayout : Bool → Fin 3 ⊕ Fin 5 ≃ Fin 8
  | false => finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [1,2,3,0,4,5,6,7] (by decide +kernel) (by decide +kernel))
  | true => finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
      [0,2,3,1,4,5,6,7] (by decide +kernel) (by decide +kernel))
def copyProgram (which : Bool) (l : Fin 2) := TM2StackFrame.relocate (copyLayout which)
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program l)
def parseLayout : Fin 4 ⊕ Fin 4 ≃ Fin 8 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [2,3,4,5,0,1,6,7] (by decide +kernel) (by decide +kernel))
def parseProgram (l : Fin 3) := TM2StackFrame.relocate parseLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.parsePorts
    PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory NatPrefixMachine.program l)
def subLayout : Fin 6 ⊕ Fin 2 ≃ Fin 8 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [2,5,3,4,6,7,0,1] (by decide +kernel) (by decide +kernel))
def subProgram (l : Fin 11) := TM2StackFrame.relocate subLayout
  (TM2FiniteCoordinates.program BinaryModAddMachine.subPorts
    BinaryModAddMachine.subLabels BinaryModuloCode.memory BinarySubtractMachine.program l)
def copyLabel (which : Bool) (l : Fin 2) : Fin 21 := ⟨3+2*which.toNat+l.val,by cases which <;> simp <;> omega⟩
def parseLabel (l : Fin 3) : Fin 21 := ⟨7+l.val,by omega⟩
def subLabel (l : Fin 11) : Fin 21 := ⟨10+l.val,by omega⟩
private def fail : Stmt (fun _ : Fin 8 => Bool) (Fin 21) (Fin 3) := .load (fun _ => 1) .halt
private def success : Stmt (fun _ : Fin 8 => Bool) (Fin 21) (Fin 3) := .load (fun _ => 2) .halt
private def enter (l : Fin 21) : Stmt (fun _ : Fin 8 => Bool) (Fin 21) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
def program (l : Fin 21) : Stmt (fun _ : Fin 8 => Bool) (Fin 21) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2) (enter (copyLabel false 0)) fail
  else if l = 1 then .branch (fun v => v == 2)
    (.peek 2 (fun _ b => BinaryModuloCode.memory b) (.branch (fun v => v == 0)
      (enter (copyLabel true 0)) fail)) fail
  else if l = 2 then .branch (fun v => v == 2) success fail
  else if h : l.val < 5 then TM2ReturnLink.redirect (copyLabel false) (parseLabel 0)
    (copyProgram false ⟨l.val-3,by omega⟩)
  else if h : l.val < 7 then TM2ReturnLink.redirect (copyLabel true) (subLabel 0)
    (copyProgram true ⟨l.val-5,by omega⟩)
  else if h : l.val < 10 then TM2ReturnLink.redirect parseLabel 1
    (parseProgram ⟨l.val-7,by omega⟩)
  else TM2ReturnLink.redirect subLabel 2 (subProgram ⟨l.val-10,by omega⟩)
def code : BitOracleMachine.Code 8 21 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 8 21 3
def tick : Config → Config := TM2ReturnLink.tick program
def start (q record : List Bool) : Config := ⟨some 0,2,![q,record,[],[],[],[],[],[]]⟩
def result (q record e complement : List Bool) : Config := ⟨none,2,![q,record,[],[],[],e,[],complement]⟩
def clock (q : Nat) := 10*(q-1).size+5*q.size+17

end ExplainableCrypto.Helios.Computational.ScalarComplementMachine
