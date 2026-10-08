import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded
import ExplainableCrypto.Helios.Computational.BitOracleTapeBoundedCanary

/-! The adaptive source canary derives its own primitive clock and preserves
complete lawful handler effects, without supplied source or compiler bounds. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCanary
open Turing OracleComp OracleSpec TM2TapeRuns BitOracleCanary OracleTapeOutput
open BitOracleLoopBounded (Within adapter)

private theorem initial_height (word : List Bool) : height (initial word).stk = word.length := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i <;> simp [initial]
  · exact length_le_height (initial word).stk 0

/-- Fixed code factor times the source-derived tape clock. This noncomputable
bound is proof-side accounting, not an instruction computing its own budget. -/
noncomputable def clock (limit : Nat) (word previous : List Bool) : Nat :=
  BitOracleTapeBoundedCanary.clock limit word previous * BitOraclePrimitiveLoop.globalFactor code

/-- All permitted adaptive answer branches agree at the derived primitive
clock. The source's own halt/charge proof supplies every algorithmic premise. -/
theorem run (limit : Nat) (word previous : List Bool) (oldAnswer : Tape (Option Bool)) :
    BitOraclePrimitiveBounded.observe <$> simulateQ (adapter limit)
      (BitOraclePrimitiveLoop.run code (clock limit word previous)
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready (initial word) (wordTape previous) oldAnswer))) =
      (fun out => some out.1) <$> simulateQ (adapter limit) (source word) := by
  have hw : Within limit (4 + 2 * word.length + 4 * limit)
      (BitOracleMachine.run code 4 (initial word)) := by
    rw [BitOracleCanary.run_source]
    exact BitOracleBoundedCanary.within limit word
  simpa only [clock, BitOracleTapeBoundedCanary.clock, initial_height, BitOracleCanary.run_source] using
    BitOraclePrimitiveBounded.run_source_bounded code 4 limit (4 + 2 * word.length + 4 * limit)
      (initial word) previous oldAnswer hw

/-- Stateful/probabilistic handler effects are preserved at the same source-
derived clock, with no caller cost, termination or compiler certificate. -/
theorem run_handler {M : Type → Type} [Monad M] [LawfulMonad M]
    (limit : Nat) (word previous : List Bool) (oldAnswer : Tape (Option Bool))
    (handler : QueryImpl (BitOracleLoopBounded.spec limit) M) :
    BitOraclePrimitiveBounded.observe <$> simulateQ handler (simulateQ (adapter limit)
      (BitOraclePrimitiveLoop.run code (clock limit word previous)
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready (initial word) (wordTape previous) oldAnswer)))) =
      (fun out => some out.1) <$> simulateQ handler (simulateQ (adapter limit) (source word)) := by
  simpa only [simulateQ_map] using congrArg (simulateQ handler) (run limit word previous oldAnswer)

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCanary
