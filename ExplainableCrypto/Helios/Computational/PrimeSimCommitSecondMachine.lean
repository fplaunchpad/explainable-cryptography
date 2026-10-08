import ExplainableCrypto.Helios.Computational.PrimeSimCommitCallerSource


namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeSimCommitMachine.size

/-- Fixed wire permutation: use the reached pk/beta as numeric bases, keep the
first coordinate outside every work port, and return the second on new port38. -/
def layout : Fin 38 ⊕ Fin 1 ≃ Fin 39 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [17,1,2,38,4,5,6,7,8,9,10,11,12,13,14,16,15,0,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3]
    (by decide +kernel) (by decide +kernel))

def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeSimCommitMachine.program l)
def code : Code 39 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 39 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (original : Fin 38 → List Bool) : Fin 39 → List Bool :=
  fun k => if h : k.val < 38 then original ⟨k.val,h⟩ else []
def start (original : Fin 38 → List Bool) : Config := ⟨some 0,2,initialWords original⟩
def result (answer : List Bool) (original : Fin 38 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords original) 38 answer⟩
def clock (p q : Nat) := PrimeSimCommitMachine.clock p q
def cost (p q : Nat) := PrimeSimCommitMachine.cost p q

/-- The actual code is the existing controller's frame relocation. -/
theorem code_frame : code = BitOracleStackFrame.code layout PrimeSimCommitMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine
