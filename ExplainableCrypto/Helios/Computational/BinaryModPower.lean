import ExplainableCrypto.Helios.Computational.BinaryModMultiply

/-! Loaded square-and-multiply required by historical encryption coordinates.
Existing multiplication and copying are called through finite return labels.
The original base/exponent and opaque caller data are retained. This file is
executable code; its general execution/cost correspondence is a separate proof. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModPower
open Turing.TM2

def layout : Fin 11 ⊕ Fin 4 ≃ Fin 15 := finSumFinEquiv
private def copyTable (which : Fin 5) : List (Fin 15) :=
  ![[8,1,2,3,4,5,13,7,0,6,9,10,11,12,14],
    [10,1,2,3,4,5,0,7,6,8,9,11,12,13,14],
    [8,1,2,3,4,5,0,7,6,9,10,11,12,13,14],
    [10,1,2,3,4,5,0,7,6,8,9,11,12,13,14],
    [8,1,2,3,4,5,11,7,0,6,9,10,12,13,14]] which

def copyLayout (which : Fin 5) : Fin 8 ⊕ Fin 7 ≃ Fin 15 :=
  finSumFinEquiv.trans
    ((finCongr (show 15 = (copyTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (copyTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def copyProgram (which : Fin 5) (l : Fin 2) :=
  TM2StackFrame.relocate (copyLayout which) (BinaryModAddMachine.copyProgram 1 l)
def multiplyProgram (l : Fin 86) :=
  TM2StackFrame.relocate layout (BinaryModMultiply.program l)

def multiplyLabel (product : Bool) (l : Fin 86) : Fin 192 :=
  ⟨10+86*product.toNat+l.val,by cases product <;> simp <;> omega⟩
def copyLabel (which : Fin 5) (l : Fin 2) : Fin 192 :=
  ⟨182+2*which.val+l.val,by omega⟩
def copyReturn (which : Fin 5) : Fin 192 :=
  ![0,copyLabel 2 0,3,copyLabel 4 0,7] which

def enter (next : Fin 192) : Stmt (fun _ : Fin 15 => Bool) (Fin 192) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
def clear (port : Fin 15) (again next : Fin 192) :
    Stmt (fun _ : Fin 15 => Bool) (Fin 192) (Fin 3) :=
  .pop port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter next) (.goto (fun _ => again)))
def guard (next : Fin 192) : Stmt (fun _ : Fin 15 => Bool) (Fin 192) (Fin 3) :=
  .branch (fun v => v == 2) (enter next) (.load (fun _ => 1) .halt)

def control (l : Fin 10) : Stmt (fun _ : Fin 15 => Bool) (Fin 192) (Fin 3) :=
  ![.pop 8 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (enter 1)
        (.push 12 (fun v => v == 2) (.goto (fun _ => 0)))),
    .push 0 (fun _ => true) (enter 2),
    .peek 12 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (enter (copyLabel 1 0))),
    clear 0 3 (multiplyLabel false (BinaryModMultiply.copyLabel 0)),
    guard 5,
    clear 10 5 6,
    .pop 12 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 2) (enter (copyLabel 3 0))
        (.branch (fun v => v == 1) (enter 2) (.load (fun _ => 1) .halt))),
    clear 0 7 (multiplyLabel true (BinaryModMultiply.copyLabel 0)),
    guard 9,
    clear 10 9 2] l

def program (l : Fin 192) : Stmt (fun _ : Fin 15 => Bool) (Fin 192) (Fin 3) :=
  if h : l.val < 10 then control ⟨l.val,h⟩
  else if h : l.val < 96 then
    TM2ReturnLink.redirect (multiplyLabel false) 4
      (multiplyProgram ⟨l.val-10,by omega⟩)
  else if h : l.val < 182 then
    TM2ReturnLink.redirect (multiplyLabel true) 8
      (multiplyProgram ⟨l.val-96,by omega⟩)
  else
    let which : Fin 5 := ⟨(l.val-182)/2,by omega⟩
    TM2ReturnLink.redirect (copyLabel which) (copyReturn which)
      (copyProgram which ⟨(l.val-182)%2,Nat.mod_lt _ (by decide)⟩)

def code : BitOracleMachine.Code 15 192 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 15 192 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (base exponent modulus context : List Bool) : Config :=
  ⟨some (copyLabel 0 0),0,![[],[],[],[],[],[],modulus,[],[],[],[],base,[],exponent,context]⟩
def result (answer base exponent modulus context : List Bool) : Config :=
  ⟨none,2,![answer,[],[],[],[],[],modulus,[],[],[],[],base,[],exponent,context]⟩

/-- Analytical bound proved in BinaryModPowerRun; the code never evaluates a host clock. -/
def clock (p width : Nat) : Nat :=
  3*width+5+width*(2*BinaryModMultiply.clock p p.size+12*p.size+16)

end ExplainableCrypto.Helios.Computational.BinaryModPower
