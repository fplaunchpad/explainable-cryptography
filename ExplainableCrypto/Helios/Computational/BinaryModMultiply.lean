import ExplainableCrypto.Helios.Computational.BinaryModAddMachine

/-! Loaded modular multiplication for public coordinates. The controller derives
p-x by actual subtraction, then scans multiplier bits from most significant to
least. Existing remainder updates perform doubling; the scoped add controller
handles one bits. No exponent-value iteration or host arithmetic is executed. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModMultiply
open Turing.TM2

def layout : Fin 8 ⊕ Fin 3 ≃ Fin 11 := finSumFinEquiv
private def coreTable (which : Fin 2) : List (Fin 11) :=
  ![[0,10,2,3,4,1,5,6,7,8,9],[0,6,2,3,4,5,1,7,8,9,10]] which

def coreLayout (which : Fin 2) : BinarySubtractMachine.Stack ⊕ Fin 5 ≃ Fin 11 :=
  ((Equiv.sumCongr BinaryModAddMachine.subPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 11 = (coreTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (coreTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def coreProgram (which : Fin 2) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 11)) BinaryModAddMachine.subLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (coreLayout which) (BinarySubtractMachine.program l))
def corePresent (which : Fin 2) (cfg : BinarySubtractMachine.Config) (frame : Fin 5 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 11)) BinaryModAddMachine.subLabels BinaryModuloCode.memory
    (TM2StackFrame.embed (coreLayout which) cfg frame)
def copyProgram (l : Fin 2) := TM2StackFrame.relocate layout (BinaryModAddMachine.copyProgram 1 l)
def addProgram (l : Fin 42) := TM2StackFrame.relocate layout (BinaryModAddMachine.program l)

def prepLabel (l : Fin 11) : Fin 86 := ⟨9+l.val,by omega⟩
def doubleLabel (b : Bool) (l : Fin 11) : Fin 86 := ⟨20+11*b.toNat+l.val,by cases b <;> simp <;> omega⟩
def addLabel (l : Fin 42) : Fin 86 := ⟨42+l.val,by omega⟩
def copyLabel (l : Fin 2) : Fin 86 := ⟨84+l.val,by omega⟩
def toTemp (b : Bool) : Fin 86 := if b then 3 else 2
def toLeft (b : Bool) : Fin 86 := if b then 5 else 4

def enter (next : Fin 86) : Stmt (fun _ : Fin 11 => Bool) (Fin 86) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
def move (source dest : Fin 11) (again next : Fin 86) :
    Stmt (fun _ : Fin 11 => Bool) (Fin 86) (Fin 3) :=
  .pop source (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter next)
      (.push dest (fun v => v == 2) (.goto (fun _ => again))))

def control (l : Fin 9) : Stmt (fun _ : Fin 11 => Bool) (Fin 86) (Fin 3) :=
  ![move 8 9 0 1,
    .pop 9 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (enter 8)
        (.branch (fun v => v == 2) (enter (doubleLabel true 4)) (enter (doubleLabel false 4)))),
    move 5 3 2 4,move 5 3 3 5,
    move 3 0 4 1,move 3 0 5 (addLabel 5),
    .branch (fun v => v == 2) (enter 0) (.load (fun _ => 1) .halt),
    .branch (fun v => v == 2) (enter 1) (.load (fun _ => 1) .halt),
    .pop 1 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (.goto (fun _ => 8)))] l

def program (l : Fin 86) : Stmt (fun _ : Fin 11 => Bool) (Fin 86) (Fin 3) :=
  if h : l.val < 9 then control ⟨l.val,h⟩
  else if h : l.val < 20 then
    TM2ReturnLink.redirect prepLabel 6 (coreProgram 0 ⟨l.val-9,by omega⟩)
  else if h : l.val < 31 then
    TM2ReturnLink.redirect (doubleLabel false) (toTemp false) (coreProgram 1 ⟨l.val-20,by omega⟩)
  else if h : l.val < 42 then
    TM2ReturnLink.redirect (doubleLabel true) (toTemp true) (coreProgram 1 ⟨l.val-31,by omega⟩)
  else if h : l.val < 84 then
    TM2ReturnLink.redirect addLabel 7 (addProgram ⟨l.val-42,by omega⟩)
  else TM2ReturnLink.redirect copyLabel (prepLabel 0) (copyProgram ⟨l.val-84,by omega⟩)

def code : BitOracleMachine.Code 11 86 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 11 86 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (x raw modulus : List Bool) : Config :=
  ⟨some (copyLabel 0),0,![[],[],[],[],[],[],modulus,[],raw,[],x]⟩
def result (answer x modulus : List Bool) : Config :=
  ⟨none,2,![answer,[],[],[],[],[],modulus,[],[],[],x]⟩
def clock (p width : Nat) : Nat := 9*p.size+11+width*(34*p.size+38)

end ExplainableCrypto.Helios.Computational.BinaryModMultiply
