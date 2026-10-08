import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineSpec

/-! Fixed relocation for the second proof's first one-branch coordinate. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondOneFirstMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeSimCommitMachine.size

def layout : Fin 38 ⊕ Fin 31 ≃ Fin 69 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [51,59,58,68,61,62,6,55,63,64,54,66,57,52,49,15,16,50,53,19,21,20,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,0,1,2,3,4,5,7,8,9,10,11,12,13,14,17,18,38,39,40,41,42,43,44,45,46,47,48,56,60,65,67]
    (by decide +kernel) (by decide +kernel))
def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeSimCommitMachine.program l)
def code : Code 69 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 69 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 68 → List Bool) : Fin 69 → List Bool :=
  fun k => if h : k.val < 68 then old ⟨k.val,h⟩ else []
def start (old : Fin 68 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (answer : List Bool) (old : Fin 68 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 68 answer⟩
def clock (p q : Nat) := PrimeSimCommitMachine.clock p q
def cost (p q : Nat) := PrimeSimCommitMachine.cost p q

def localFrame (old : Fin 68 → List Bool) : Fin 11 → List Bool :=
  ![old 51,old 55,old 54,old 52,old 49,old 15,old 53,old 19,old 21,old 20,old 22]
def frame (old : Fin 68 → List Bool) : Fin 31 → List Bool := fun k =>
  old ⟨(layout (.inr k)).val,by fin_cases k <;> decide +kernel⟩

/-- Only a stack relocation; original arithmetic and local charge bounds are unchanged. -/
theorem code_frame : code = BitOracleStackFrame.code layout PrimeSimCommitMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSecondOneFirstMachine
