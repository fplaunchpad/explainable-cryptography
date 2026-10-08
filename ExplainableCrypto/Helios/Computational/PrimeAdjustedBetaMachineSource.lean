import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaOrigins
import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineRun
import ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource

namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
open OracleComp BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  result (primeGroupCoordinate ((encryptWith g pk out.1.1 (voteScalar vote)).2-g)).val.bits
    (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk

/-- Every operand, width and blank-work requirement comes from the reached
source result. The adjusted group element uses actual beta and g. -/
theorem charged_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  obtain ⟨charge,hc,he⟩ := charged p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).2).val
    (Fact.out : p.Prime).two_le (ZMod.val_lt _) (ZMod.val_lt _)
    (retained (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk)
  rw [inputWords_source] at he
  have ha := PrimeSimCommitOneSource.adjusted_beta_value
    (encryptWith g pk out.1.1 (voteScalar vote)).2 g
  change _ = answer p q (primeGroupCoordinate g).val
    (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).2).val at ha
  rw [←ha] at he
  exact ⟨charge,hc,he⟩

theorem source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk) =
    pure (sourceResult slack g pk vote saved out) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote saved out
  rw [he,map_pure]

#print axioms charged_source
#print axioms source
end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
