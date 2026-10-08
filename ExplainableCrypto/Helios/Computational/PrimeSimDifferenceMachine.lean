import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachine
import ExplainableCrypto.Helios.Computational.PrimeSimCommitPairCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 65536
abbrev size := ScalarDifferenceMachine.size
/-- Existing private work hosts both decoders and arithmetic; port1 holds d.
Every original input and both zero-branch commitments remain outside scratch. -/
def layout : Fin 10 ⊕ Fin 29 ≃ Fin 39 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [2,10,11,1,23,24,25,26,27,28,0,3,4,5,6,7,8,9,12,13,14,15,16,17,18,19,20,21,22,29,30,31,32,33,34,35,36,37,38] (by decide +kernel) (by decide +kernel))
def program (l : Fin size) := TM2StackFrame.relocate layout (ScalarDifferenceMachine.program l)
def code : Code 39 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 39 size 3
def start (original : Fin 39 → List Bool) : Config := ⟨some 0,2,original⟩
def result (answer : List Bool) (original : Fin 39 → List Bool) : Config :=
  ⟨none,2,Function.update original 1 answer⟩
def clock (q : Nat) := ScalarDifferenceMachine.clock q
def cost (q : Nat) := ScalarDifferenceMachine.cost q
theorem code_frame : code = BitOracleStackFrame.code layout ScalarDifferenceMachine.code := rfl
end ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine
