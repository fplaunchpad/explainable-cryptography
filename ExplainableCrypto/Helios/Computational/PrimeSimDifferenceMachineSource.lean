import ExplainableCrypto.Helios.Computational.PrimeSimDifferenceOrigins
import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine
open OracleComp BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

/-- Exact canonical challenge difference, alongside the complete earlier state. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  result (uniformNatEncode (out.2.1-out.2.2.1).val)
    (PrimeSimCommitPairCaller.sourceResult slack g pk vote saved out).stk

/-- The actual source supplies every encoded operand and blank work condition.
Framing preserves the exact query-free execution and its derived charge. -/
theorem charged_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ∃ charge ≤ cost q,
      BitOracleMachine.run code (clock q)
        (start (PrimeSimCommitPairCaller.sourceResult slack g pk vote saved out).stk) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  obtain ⟨charge,hc,he⟩ := ScalarDifferenceMachine.charged_source out.2.1 out.2.2.1
  have hf := BitOracleStackFrame.run layout ScalarDifferenceMachine.code
    (ScalarDifferenceMachine.clock q)
    (ScalarDifferenceMachine.start q.bits (uniformNatEncode out.2.1.val)
      (uniformNatEncode out.2.2.1.val))
    (retained (PrimeSimCommitPairCaller.sourceResult slack g pk vote saved out).stk)
  rw [he,map_pure,←code_frame,source_inputs,source_outputs] at hf
  exact ⟨charge,hc,hf⟩

theorem source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    Prod.fst <$> BitOracleMachine.run code (clock q)
      (start (PrimeSimCommitPairCaller.sourceResult slack g pk vote saved out).stk) =
    pure (sourceResult slack g pk vote saved out) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote saved out
  rw [he,map_pure]

#print axioms charged_source
#print axioms source
end ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine
