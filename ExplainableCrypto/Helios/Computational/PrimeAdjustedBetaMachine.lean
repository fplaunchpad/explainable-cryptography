import ExplainableCrypto.Helios.Computational.BinaryModPowerRun
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink

namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
open Turing.TM2 OracleComp BitOracleMachine

def size : Nat := 280
instance : NeZero size := ⟨by decide⟩

def powerLayout : Fin 15 ⊕ Fin 25 ≃ Fin 40 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [23,24,25,26,27,28,6,29,30,31,32,16,33,22,14,
     0,1,2,3,4,5,7,8,9,10,11,12,13,15,17,18,19,20,21,34,35,36,37,38,39]
    (by decide +kernel) (by decide +kernel))
def multiplyLayout : Fin 11 ⊕ Fin 29 ≃ Fin 40 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [39,24,25,26,27,28,6,29,23,30,0,
     1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,31,32,33,34,35,36,37,38]
    (by decide +kernel) (by decide +kernel))

def powerProgram (l : Fin 192) := TM2StackFrame.relocate powerLayout (BinaryModPower.program l)
def multiplyProgram (l : Fin 86) := TM2StackFrame.relocate multiplyLayout (BinaryModMultiply.program l)
def powerLabel (l : Fin 192) : Fin size := ⟨2+l.val,by have := l.isLt; unfold size; omega⟩
def multiplyLabel (l : Fin 86) : Fin size := ⟨194+l.val,by have := l.isLt; unfold size; omega⟩

def guard (next : Fin size) : Stmt (fun _ : Fin 40 => Bool) (Fin size) (Fin 3) :=
  .branch (fun v => v == 2) (.load (fun _ => 0) (.goto (fun _ => next)))
    (.load (fun _ => 1) .halt)

def program (l : Fin size) : Stmt (fun _ : Fin 40 => Bool) (Fin size) (Fin 3) :=
  if h : l.val < 2 then
    if l.val = 0 then guard (powerLabel (BinaryModPower.copyLabel 0 0))
    else guard (multiplyLabel (BinaryModMultiply.copyLabel 0))
  else if h : l.val < 194 then
    BitOracleReturnLink.stmt powerLabel (some 1) (powerProgram ⟨l.val-2,by omega⟩)
  else BitOracleReturnLink.stmt multiplyLabel none
    (multiplyProgram ⟨l.val-194,by have := l.isLt; unfold size at this; omega⟩)

def code : Code 40 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 40 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def inputWords (p q g beta : Nat) (frame : Fin 20 → List Bool) : Fin 39 → List Bool :=
  ![beta.bits,frame 0,frame 1,frame 2,frame 3,frame 4,p.bits,frame 5,frame 6,frame 7,
    frame 8,frame 9,frame 10,frame 11,frame 12,frame 13,g.bits,frame 14,frame 15,
    frame 16,frame 17,frame 18,(q-1).bits,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],frame 19]
def initialWords (old : Fin 39 → List Bool) : Fin 40 → List Bool :=
  fun k => if h : k.val < 39 then old ⟨k.val,h⟩ else []
def start (old : Fin 39 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (answer : List Bool) (old : Fin 39 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 39 answer⟩
def answer (p q g beta : Nat) := (beta*(g^(q-1)%p))%p

def clock (p q : Nat) :=
  BinaryModPower.clock p (q-1).size + BinaryModMultiply.clock p p.size + 2
def cost (p q : Nat) := 32*clock p q

end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
