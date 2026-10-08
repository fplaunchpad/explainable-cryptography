import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
import ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def retained (old : Fin 39 → List Bool) : Fin 20 → List Bool :=
  ![old 1,old 2,old 3,old 4,old 5,old 7,old 8,old 9,old 10,old 11,old 12,old 13,old 14,old 15,old 17,old 18,old 19,old 20,old 21,old 38]

/-- The actual difference result retains beta/g/p and q−1, and all power work
is empty. Earlier coordinates and the new difference prefix remain in frame. -/
theorem inputWords_source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out
    inputWords p q (primeGroupCoordinate g).val
      (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).2).val
      (retained old.stk) = old.stk := by
  dsimp only
  funext k; fin_cases k <;> rfl

#print axioms inputWords_source
end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
