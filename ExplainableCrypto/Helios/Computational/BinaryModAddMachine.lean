import ExplainableCrypto.Helios.Computational.BinaryModuloCode
import ExplainableCrypto.Helios.Computational.BitCopyMachine
import ExplainableCrypto.Helios.Computational.TM2StackFrame

/-! Reduced addition required by the modular multiplier. The retained complement
c=p-x is an inner interface; the multiplier must execute its preparation. This
controller uses the existing subtraction and copying programs, with no host
arithmetic or whole-word update in its executable instructions. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModAddMachine
open Turing.TM2

def subPorts : BinarySubtractMachine.Stack ≃ Fin 6 where
  toFun | .left => 0 | .right => 1 | .diff => 2 | .savedLeft => 3 | .savedRight => 4 | .out => 5
  invFun := ![.left,.right,.diff,.savedLeft,.savedRight,.out]
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def subLabels : BinarySubtractMachine.Label ≃ Fin 11 where
  toFun
    | .scan false => 0 | .scan true => 1
    | .restoreRight false => 2 | .restoreRight true => 3
    | .shift false => 4 | .shift true => 5
    | .clearDiff => 6 | .restoreLeft => 7 | .clearLeft => 8 | .trim => 9 | .reverse => 10
  invFun := ![.scan false,.scan true,.restoreRight false,.restoreRight true,
    .shift false,.shift true,.clearDiff,.restoreLeft,.clearLeft,.trim,.reverse]
  left_inv l := by cases l <;> first | rfl | (rename_i b; cases b <;> rfl)
  right_inv l := by fin_cases l <;> rfl

private def subTable (which : Fin 3) : List (Fin 8) :=
  ![[0,1,2,3,4,5,6,7],[0,5,2,3,4,7,1,6],[0,7,2,3,4,5,1,6]] which

def subLayout (which : Fin 3) : BinarySubtractMachine.Stack ⊕ Fin 2 ≃ Fin 8 :=
  ((Equiv.sumCongr subPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 8 = (subTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (subTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def subProgram (which : Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 8)) subLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (subLayout which) (BinarySubtractMachine.program l))
def subPresent (which : Fin 3) (cfg : BinarySubtractMachine.Config) (frame : Fin 2 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 8)) subLabels BinaryModuloCode.memory
    (TM2StackFrame.embed (subLayout which) cfg frame)

private def copyPorts : BitCopyMachine.Stack ≃ Fin 3 where
  toFun | .source => 0 | .destination => 1 | .scratch => 2
  invFun := ![.source,.destination,.scratch]
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
private def copyLabels : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun k := k == 1
  left_inv b := by cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl
private def copyTable (which : Fin 2) : List (Fin 8) :=
  ![[1,0,2,3,4,5,6,7],[6,0,2,1,3,4,5,7]] which

def copyLayout (which : Fin 2) : BitCopyMachine.Stack ⊕ Fin 5 ≃ Fin 8 :=
  ((Equiv.sumCongr copyPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 8 = (copyTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (copyTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def copyProgram (which : Fin 2) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 8)) copyLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (copyLayout which) (BitCopyMachine.program l))
def copyPresent (which : Fin 2) (cfg : BitCopyMachine.Config) (frame : Fin 5 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 8)) copyLabels BinaryModuloCode.memory
    (TM2StackFrame.embed (copyLayout which) cfg frame)

def subLabel (which : Fin 3) (l : Fin 11) : Fin 42 := ⟨5+11*which.val+l.val,by omega⟩
def copyLabel (which : Fin 2) (l : Fin 2) : Fin 42 := ⟨38+2*which.val+l.val,by omega⟩
def subReturn (which : Fin 3) : Fin 42 := ⟨which.val,by omega⟩
def copyReturn (which : Fin 2) : Fin 42 := if which = 0 then subLabel 1 0 else subLabel 2 0

def enter (next : Fin 42) : Stmt (fun _ : Fin 8 => Bool) (Fin 42) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
def clear (port : Fin 8) (again next : Fin 42) : Stmt (fun _ : Fin 8 => Bool) (Fin 42) (Fin 3) :=
  .pop port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter next) (.goto (fun _ => again)))

def control (l : Fin 5) : Stmt (fun _ : Fin 8 => Bool) (Fin 42) (Fin 3) :=
  ![.branch (fun v => v == 2) (enter 3)
      (.branch (fun v => v == 1) (enter (copyLabel 0 0)) (.load (fun _ => 1) .halt)),
    clear 5 1 (copyLabel 1 0),clear 7 2 3,
    .pop 5 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (enter 4)
        (.push 3 (fun v => v == 2) (.goto (fun _ => 3)))),
    .pop 3 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt)
        (.push 0 (fun v => v == 2) (.goto (fun _ => 4))))] l

def program (l : Fin 42) : Stmt (fun _ : Fin 8 => Bool) (Fin 42) (Fin 3) :=
  if h : l.val < 5 then control ⟨l.val,h⟩
  else if h : l.val < 38 then
    let which : Fin 3 := ⟨(l.val-5)/11,by omega⟩
    TM2ReturnLink.redirect (subLabel which) (subReturn which)
      (subProgram which ⟨(l.val-5)%11,Nat.mod_lt _ (by decide)⟩)
  else
    let which : Fin 2 := ⟨(l.val-38)/2,by omega⟩
    TM2ReturnLink.redirect (copyLabel which) (copyReturn which)
      (copyProgram which ⟨(l.val-38)%2,Nat.mod_lt _ (by decide)⟩)

def code : BitOracleMachine.Code 8 42 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 8 42 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (r complement modulus : List Bool) : Config :=
  ⟨some (subLabel 0 0),0,![r,complement,[],[],[],[],modulus,[]]⟩
def result (answer complement modulus : List Bool) : Config :=
  ⟨none,2,![answer,complement,[],[],[],[],modulus,[]]⟩
def clock (p : Nat) : Nat := 26*p.size+24

end ExplainableCrypto.Helios.Computational.BinaryModAddMachine
