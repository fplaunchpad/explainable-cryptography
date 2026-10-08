import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine

/-! Fixed executed p1 operand preparation; original words remain resident. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := ScalarDifferenceMachine.size
set_option maxRecDepth 65536

def layout : Fin 10 ⊕ Fin 57 ≃ Fin 67 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [58,54,55,66,23,24,25,26,27,28,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,56,57,59,60,61,62,63,64,65] (by decide +kernel) (by decide +kernel))
def program (l : Fin size) := TM2StackFrame.relocate layout (ScalarDifferenceMachine.program l)
def code : Code 67 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 67 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 66 → List Bool) : Fin 67 → List Bool :=
  fun k => if h : k.val < 66 then old ⟨k.val,h⟩ else []
def start (old : Fin 66 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (answer : List Bool) (old : Fin 66 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 66 answer⟩
def frame (old : Fin 66 → List Bool) : Fin 57 → List Bool := fun k =>
  old ⟨(layout (.inr k)).val,by fin_cases k <;> decide +kernel⟩
def clock (q : Nat) := ScalarDifferenceMachine.clock q
def cost (q : Nat) := ScalarDifferenceMachine.cost q
theorem code_frame : code = BitOracleStackFrame.code layout ScalarDifferenceMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachine
