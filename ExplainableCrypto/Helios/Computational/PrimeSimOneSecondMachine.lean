import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineRun


namespace ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeSimCommitMachine.size

/-- Fixed wire permutation: use the reached pk/adjusted-beta as numeric bases, keep the
previous three coordinates outside every work port, and return the fourth on42. -/
def layout : Fin 38 ⊕ Fin 5 ≃ Fin 43 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,41,2,42,4,5,6,11,8,9,10,1,7,13,14,16,15,39,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3,12,17,38,40]
    (by decide +kernel) (by decide +kernel))

def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeSimCommitMachine.program l)
def code : Code 43 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 43 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (original : Fin 42 → List Bool) : Fin 43 → List Bool :=
  fun k => if h : k.val < 42 then original ⟨k.val,h⟩ else []
def start (original : Fin 42 → List Bool) : Config := ⟨some 0,2,initialWords original⟩
def result (answer : List Bool) (original : Fin 42 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords original) 42 answer⟩
def clock (p q : Nat) := PrimeSimCommitMachine.clock p q
def cost (p q : Nat) := PrimeSimCommitMachine.cost p q

/-- The actual code is the existing controller's frame relocation. -/
theorem code_frame : code = BitOracleStackFrame.code layout PrimeSimCommitMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
