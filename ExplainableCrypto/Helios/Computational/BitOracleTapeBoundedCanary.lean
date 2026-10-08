import ExplainableCrypto.Helios.Computational.BitOracleTapeBounded
import ExplainableCrypto.Helios.Computational.BitOracleBoundedCanary

/-! Derive the actual tape clock for the fixed adaptive hash canary.
No source termination/cost or compiler certificate is supplied for this instance. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeBoundedCanary
open Turing OracleComp OracleSpec TM2TapeRuns BitOracleCanary OracleTapeOutput
open BitOracleLoopBounded (Within adapter)

private theorem initial_height (word : List Bool) : height (initial word).stk = word.length := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i <;> simp [initial]
  · exact length_le_height (initial word).stk 0

/-- The canary's derived source charge and actual initial/previous-query sizes. -/
def clock (limit : Nat) (word previous : List Bool) : Nat :=
  let bound := 4 + 2 * word.length + 4 * limit
  BitOracleTapeCap.unitCost (word.length + bound + previous.length) * bound

/-- Every allowed adaptive answer tree agrees at this single actual tape clock. -/
theorem run (limit : Nat) (word previous : List Bool) (oldAnswer : Tape (Option Bool)) :
    BitOracleTapeLoop.observeCaller <$> simulateQ (adapter limit)
      (BitOracleTapeLoop.run code (clock limit word previous)
        (BitOracleTapeLoop.ready (initial word) (wordTape previous) oldAnswer)) =
      (fun out => some out.1) <$> simulateQ (adapter limit) (source word) := by
  have hw : Within limit (4 + 2 * word.length + 4 * limit)
      (BitOracleMachine.run code 4 (initial word)) := by
    rw [BitOracleCanary.run_source]
    exact BitOracleBoundedCanary.within limit word
  simpa only [clock, initial_height, BitOracleCanary.run_source] using
    BitOracleTapeLoop.run_source_bounded code 4 limit (4 + 2 * word.length + 4 * limit)
      (initial word) previous oldAnswer hw

/-- The same source-derived clock preserves complete lawful handler effects. -/
theorem run_handler {M : Type → Type} [Monad M] [LawfulMonad M]
    (limit : Nat) (word previous : List Bool) (oldAnswer : Tape (Option Bool))
    (handler : QueryImpl (BitOracleLoopBounded.spec limit) M) :
    BitOracleTapeLoop.observeCaller <$> simulateQ handler (simulateQ (adapter limit)
      (BitOracleTapeLoop.run code (clock limit word previous)
        (BitOracleTapeLoop.ready (initial word) (wordTape previous) oldAnswer))) =
      (fun out => some out.1) <$> simulateQ handler (simulateQ (adapter limit) (source word)) := by
  simpa only [simulateQ_map] using congrArg (simulateQ handler) (run limit word previous oldAnswer)

end ExplainableCrypto.Helios.Computational.BitOracleTapeBoundedCanary
