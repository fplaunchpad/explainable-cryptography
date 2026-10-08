import ExplainableCrypto.Helios.Computational.BinaryModPower

/-! Concrete two-power encryption controller for the first honest ciphertext.
Public coordinates and the nonce are resident digits. Actual public-record
parsing and connection to the preceding nonce-pair layout are separate work. -/
namespace ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
open Turing.TM2

def powerLayout : Fin 15 ⊕ Fin 4 ≃ Fin 19 := finSumFinEquiv
def multiplyLayout : Fin 11 ⊕ Fin 8 ≃ Fin 19 := finSumFinEquiv
private def copyTable (which : Fin 5) : List (Fin 19) :=
  ![[11,1,2,3,4,5,16,7,0,6,8,9,10,12,13,14,15,17,18],
    [17,1,2,3,4,5,0,7,6,8,9,10,11,12,13,14,15,16,18],
    [11,1,2,3,4,5,15,7,0,6,8,9,10,12,13,14,16,17,18],
    [10,1,2,3,4,5,0,7,6,8,9,11,12,13,14,15,16,17,18],
    [8,1,2,3,4,5,16,7,0,6,9,10,11,12,13,14,15,17,18]] which

def copyLayout (which : Fin 5) : Fin 8 ⊕ Fin 11 ≃ Fin 19 :=
  finSumFinEquiv.trans
    ((finCongr (show 19 = (copyTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (copyTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def copyProgram (which : Fin 5) (l : Fin 2) :=
  TM2StackFrame.relocate (copyLayout which) (BinaryModAddMachine.copyProgram 1 l)
def powerProgram (l : Fin 192) :=
  TM2StackFrame.relocate powerLayout (BinaryModPower.program l)
def multiplyProgram (l : Fin 86) :=
  TM2StackFrame.relocate multiplyLayout (BinaryModMultiply.program l)

def powerLabel (which : Fin 2) (l : Fin 192) : Fin 490 :=
  ⟨10+192*which.val+l.val,by omega⟩
def multiplyLabel (l : Fin 86) : Fin 490 := ⟨394+l.val,by omega⟩
def copyLabel (which : Fin 5) (l : Fin 2) : Fin 490 :=
  ⟨480+2*which.val+l.val,by omega⟩
def powerReturn (which : Fin 2) : Fin 490 := if which = 0 then 0 else 3
def copyReturn (which : Fin 5) : Fin 490 :=
  ![powerLabel 0 (BinaryModPower.copyLabel 0 0),1,
    powerLabel 1 (BinaryModPower.copyLabel 0 0),copyLabel 4 0,5] which

def enter (next : Fin 490) : Stmt (fun _ : Fin 19 => Bool) (Fin 490) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
def clear (port : Fin 19) (again next : Fin 490) :
    Stmt (fun _ : Fin 19 => Bool) (Fin 490) (Fin 3) :=
  .pop port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (enter next) (.goto (fun _ => again)))
def guard (next : Fin 490) : Stmt (fun _ : Fin 19 => Bool) (Fin 490) (Fin 3) :=
  .branch (fun v => v == 2) (enter next) (.load (fun _ => 1) .halt)

def control (l : Fin 10) : Stmt (fun _ : Fin 19 => Bool) (Fin 490) (Fin 3) :=
  ![guard (copyLabel 1 0),
    clear 0 1 2,
    clear 11 2 (copyLabel 2 0),
    guard 4,
    .peek 18 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 2) (enter (copyLabel 3 0))
        (.branch (fun v => v == 1) (enter 8) (.load (fun _ => 1) .halt))),
    clear 0 5 (multiplyLabel (BinaryModMultiply.copyLabel 0)),
    guard 7,
    clear 10 7 8,
    clear 11 8 9,
    .load (fun _ => 2) .halt] l

def program (l : Fin 490) : Stmt (fun _ : Fin 19 => Bool) (Fin 490) (Fin 3) :=
  if h : l.val < 10 then control ⟨l.val,h⟩
  else if h : l.val < 394 then
    let which : Fin 2 := ⟨(l.val-10)/192,by omega⟩
    TM2ReturnLink.redirect (powerLabel which) (powerReturn which)
      (powerProgram ⟨(l.val-10)%192,Nat.mod_lt _ (by decide)⟩)
  else if h : l.val < 480 then
    TM2ReturnLink.redirect multiplyLabel 6 (multiplyProgram ⟨l.val-394,by omega⟩)
  else
    let which : Fin 5 := ⟨(l.val-480)/2,by omega⟩
    TM2ReturnLink.redirect (copyLabel which) (copyReturn which)
      (copyProgram which ⟨(l.val-480)%2,Nat.mod_lt _ (by decide)⟩)

def code : BitOracleMachine.Code 19 490 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 19 490 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (g pk nonce modulus context : List Bool) (vote : Bool) : Config :=
  ⟨some (copyLabel 0 0),0,![[],[],[],[],[],[],modulus,[],[],[],[],[],[],nonce,context,pk,g,[],[vote]]⟩
def result (alpha beta g pk nonce modulus context : List Bool) (vote : Bool) : Config :=
  ⟨none,2,![beta,[],[],[],[],[],modulus,[],[],[],[],[],[],nonce,context,pk,g,alpha,[vote]]⟩

/-- Caller bound proved in PrimeEncryptMachineRun. -/
def clock (p width : Nat) : Nat :=
  2*BinaryModPower.clock p width+BinaryModMultiply.clock p p.size+15*p.size+20

end ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
