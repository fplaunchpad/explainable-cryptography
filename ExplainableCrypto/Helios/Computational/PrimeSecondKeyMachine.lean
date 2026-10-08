import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! Fixed reuse of the original eight-field key writer at the reached p1 state. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeSimKeyMachine.size

def layout : Fin 44 ⊕ Fin 27 ≃ Fin 71 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [51,1,2,60,4,5,6,7,8,9,10,11,12,13,14,15,16,50,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,65,39,68,41,69,70,0,3,17,38,40,42,43,44,45,46,47,48,49,52,53,54,55,56,57,58,59,61,62,63,64,66,67] (by decide +kernel) (by decide +kernel))
def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeSimKeyMachine.program l)
def code : Code 71 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 71 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 70 → List Bool) : Fin 71 → List Bool :=
  fun k => if h : k.val < 70 then old ⟨k.val,h⟩ else []
def start (old : Fin 70 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (key : List Bool) (old : Fin 70 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 70 key⟩
def clock (p : Nat) := PrimeSimKeyMachine.clock p
def cost (p : Nat) := PrimeSimKeyMachine.cost p

def localWords (old : Fin 70 → List Bool) : Fin 43 → List Bool := fun k =>
  old ⟨(layout (.inl k.castSucc)).val,by fin_cases k <;> decide +kernel⟩
def frame (old : Fin 70 → List Bool) : Fin 27 → List Bool := fun k =>
  old ⟨(layout (.inr k)).val,by fin_cases k <;> decide +kernel⟩

/-- Every original field-writing instruction is unchanged apart from ports. -/
theorem code_frame : code = BitOracleStackFrame.code layout PrimeSimKeyMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine
