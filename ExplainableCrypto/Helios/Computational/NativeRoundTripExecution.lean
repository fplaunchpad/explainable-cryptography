import ExplainableCrypto.Helios.Computational.NativeRoundTripRun
import ExplainableCrypto.Helios.Computational.NativeRoundTripSpecification
import ExplainableCrypto.Helios.Computational.BitOracleLoopBounded

namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
variable {l : Nat}

/-- One entry instruction is executed before observing the next native entry.
The observation stops at the actual live return and retains all instruction charges. -/
def execute (p : NativeOracleTape.Code l) (fuel : Nat) (cfg : Config l) :
    OracleComp BitOracleMachine.spec (Config l × Nat) := do
  let first ← BitOracleMachine.step (code p) cfg
  let last ← NativeReturnObservation.run atNative (code p) fuel first.1
  pure (last.1,first.2+last.2)

def callFuel (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (limit : Nat) :=
  exportClock h after+importClock h before after (limit+1)+4

def callCost (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (limit : Nat) :=
  8+6*exportClock h after+
    (2+(queryWord h after).length+(cells (after 2)).length+(limit+1))+
    5*importClock h before after (limit+1)

def boundedCall (limit : Nat) (kind : OracleTapeDispatch.Kind) (query : List Bool) :=
  simulateQ (BitOracleLoopBounded.adapter limit) (call kind query)

def boundedExecute (p : NativeOracleTape.Code l) (q : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (limit : Nat) :=
  simulateQ (BitOracleLoopBounded.adapter limit)
    (execute p (callFuel h before after limit) (initial q h before after))

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
