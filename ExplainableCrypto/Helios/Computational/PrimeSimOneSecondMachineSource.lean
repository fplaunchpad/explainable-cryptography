import ExplainableCrypto.Helios.Computational.PrimeSimOneSecondOrigins
import ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
open OracleComp BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

/-- Complete result of the original statement's second one-branch coordinate.
All previous42words remain literal; the final answer occupies42. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  result
    (primeGroupCoordinate (ballotSimCommit (honestProofStatement g pk (vote,out.1.1))
      out.2.1 (out.2.2.1,out.2.2.2.1,out.2.2.2.2)).2.2).val.bits
    (PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out).stk

private theorem answer_source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    PrimeSimCommitMachine.answer p q (primeGroupCoordinate pk).val
      (primeGroupCoordinate ((encryptWith g pk out.1.1 (voteScalar vote)).2-g)).val
      (out.2.1-out.2.2.1).val out.2.2.2.2.val =
    (primeGroupCoordinate (ballotSimCommit (honestProofStatement g pk (vote,out.1.1))
      out.2.1 (out.2.2.1,out.2.2.2.1,out.2.2.2.2)).2.2).val := by
  simpa only [PrimeSimCommitMachine.answer,honestProofStatement] using
    (PrimeSimCommitOneSource.second_coordinate_value (honestProofStatement g pk (vote,out.1.1))
      out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2).symm

/-- Reuse the actual numeric run under the fixed frame. The original source
supplies every operand and bound; the exact charge is preserved by relocation. -/
theorem charged_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q)
        (start (PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out).stk) =
      pure (sourceResult slack g pk vote saved out,charge) := by
  let old := PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out
  let operands := PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate pk).val
    (primeGroupCoordinate ((encryptWith g pk out.1.1 (voteScalar vote)).2-g)).val
    (out.2.1-out.2.2.1).val out.2.2.2.2.val (retained old.stk)
  obtain ⟨charge,hc,he⟩ := PrimeSimCommitMachine.charged p q (primeGroupCoordinate pk).val
    (primeGroupCoordinate ((encryptWith g pk out.1.1 (voteScalar vote)).2-g)).val
    (out.2.1-out.2.2.1).val out.2.2.2.2.val (Fact.out : p.Prime).two_le
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (retained old.stk)
  have hf := BitOracleStackFrame.run layout PrimeSimCommitMachine.code
    (PrimeSimCommitMachine.clock p q) (PrimeSimCommitMachine.start operands) ![old.stk 3,old.stk 12,old.stk 17,old.stk 38,old.stk 40]
  dsimp only [operands,old] at hf he
  rw [he,map_pure,←code_frame,source_inputs,source_outputs,answer_source] at hf
  exact ⟨charge,hc,hf⟩

/-- Complete query-free final-coordinate source law from the reached first
one-branch state. Private data and all earlier results are preserved. -/
theorem source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    Prod.fst <$> BitOracleMachine.run code (clock p q)
      (start (PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out).stk) =
    pure (sourceResult slack g pk vote saved out) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote saved out
  rw [he,map_pure]

#print axioms charged_source
#print axioms source
end ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
