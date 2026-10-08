import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineSource


namespace ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine
open Turing.TM2 OracleComp BitOracleMachine
abbrev size := PrimeSimCommitMachine.size

/-- Fixed wire permutation: use reached d and z1 scalar prefixes with g/alpha, retain all
prior coordinates outside work ports, and return the first one-branch value on40. -/
def layout : Fin 38 ⊕ Fin 4 ≃ Fin 42 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,41,2,40,4,5,6,11,8,9,10,1,7,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,3,12,38,39]
    (by decide +kernel) (by decide +kernel))

def program (l : Fin size) := TM2StackFrame.relocate layout (PrimeSimCommitMachine.program l)
def code : Code 42 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 42 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (original : Fin 40 → List Bool) : Fin 42 → List Bool :=
  fun k => if h : k.val < 40 then original ⟨k.val,h⟩ else []
def start (original : Fin 40 → List Bool) : Config := ⟨some 0,2,initialWords original⟩
def result (answer : List Bool) (original : Fin 40 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords original) 40 answer⟩
def clock (p q : Nat) := PrimeSimCommitMachine.clock p q
def cost (p q : Nat) := PrimeSimCommitMachine.cost p q

/-- The actual code is the existing controller's frame relocation. -/
theorem code_frame : code = BitOracleStackFrame.code layout PrimeSimCommitMachine.code := rfl

#print axioms code_frame
end ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine
