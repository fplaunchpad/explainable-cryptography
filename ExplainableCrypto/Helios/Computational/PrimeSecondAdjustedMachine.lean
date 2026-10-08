import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! Fixed executed p1 operand preparation; original words remain resident. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondAdjustedMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeAdjustedBetaMachine.size
set_option maxRecDepth 65536

def layout : Fin 40 ⊕ Fin 28 ≃ Fin 68 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [51,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,67,0,39,40,41,42,43,44,45,46,47,48,49,50,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66] (by decide +kernel) (by decide +kernel))
def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeAdjustedBetaMachine.program l)
def code : Code 68 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 68 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 67 → List Bool) : Fin 68 → List Bool :=
  fun k => if h : k.val < 67 then old ⟨k.val,h⟩ else []
def start (old : Fin 67 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (answer : List Bool) (old : Fin 67 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 67 answer⟩
def frame (old : Fin 67 → List Bool) : Fin 28 → List Bool := fun k =>
  old ⟨(layout (.inr k)).val,by fin_cases k <;> decide +kernel⟩
def clock (p q : Nat) := PrimeAdjustedBetaMachine.clock p q
def cost (p q : Nat) := PrimeAdjustedBetaMachine.cost p q
theorem code_frame : code = BitOracleStackFrame.code layout PrimeAdjustedBetaMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSecondAdjustedMachine
