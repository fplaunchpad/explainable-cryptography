import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineSpec

/-! Fixed relocation of the existing first-commitment controller onto the
second transcript's reached operands. The earlier 59 words remain resident. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeSimCommitMachine.size

def layout : Fin 38 ⊕ Fin 27 ≃ Fin 65 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [51,59,58,60,61,62,6,57,63,64,54,55,56,52,49,15,16,50,53,19,21,20,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,0,1,2,3,4,5,7,8,9,10,11,12,13,14,17,18,38,39,40,41,42,43,44,45,46,47,48]
    (by decide +kernel) (by decide +kernel))
def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeSimCommitMachine.program l)
def code : Code 65 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 65 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 59 → List Bool) : Fin 65 → List Bool :=
  fun k => if h : k.val < 59 then old ⟨k.val,h⟩ else []
def start (old : Fin 59 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (answer : List Bool) (old : Fin 59 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 60 answer⟩
def clock (p q : Nat) := PrimeSimCommitMachine.clock p q
def cost (p q : Nat) := PrimeSimCommitMachine.cost p q

/-- Numeric operand presentation, using the existing local eleven-word frame
and this fixed caller's twenty-seven additional retained words. -/
def inputWords (p q g alpha e z0 : Nat) (localFrame : Fin 11 → List Bool)
    (extra : Fin 27 → List Bool) : Fin 59 → List Bool := fun k =>
  TM2StackFrame.data layout
    (PrimeSimCommitMachine.initialWords (PrimeSimCommitMachine.inputWords p q g alpha e z0 localFrame))
    extra ⟨k.val,by omega⟩
def localFrame (old : Fin 59 → List Bool) : Fin 11 → List Bool :=
  ![old 51,old 57,old 54,old 52,old 49,old 15,old 53,old 19,old 21,old 20,old 22]
def frame (old : Fin 59 → List Bool) : Fin 27 → List Bool := fun k =>
  old ⟨(layout (.inr k)).val,by fin_cases k <;> decide +kernel⟩

/-- Only a stack relocation; every original arithmetic instruction is reused. -/
theorem code_frame : code = BitOracleStackFrame.code layout PrimeSimCommitMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachine
