import ExplainableCrypto.Helios.Computational.BitOracleLoopBounded
import ExplainableCrypto.Helios.Computational.BitOracleCanary

/-! The fixed adaptive hash program meets the bounded-answer execution contract.
No source halting/cost premise is supplied for this instance. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleBoundedCanary
open OracleComp OracleSpec BitOracleLoopBounded BitOracleCanary

/-- Derive the complete source charge and actual halt for every allowed branch. -/
theorem within (limit : Nat) (word : List Bool) :
    Within limit (4 + 2 * word.length + 4 * limit) (source word) := by
  change ∀ a : List Bool, a.length ≤ limit →
    ∀ b : List Bool, b.length ≤ limit →
      ∀ c : List Bool, c.length ≤ limit →
        (final word a b c).l = none ∧
          4 + 2 * word.length + 2 * a.length + b.length + c.length ≤
            4 + 2 * word.length + 4 * limit
  intro a ha b hb c hc
  exact ⟨rfl, by omega⟩

/-- The entire adaptive query tree is the actual common-clock loop observation. -/
theorem run (limit : Nat) (word : List Bool) :
    simulateQ (adapter limit)
      (BitOracleLoop.run code (11 * (4 + 2 * word.length + 4 * limit))
        (.ready (initial word))) =
      (fun out => BitOracleLoop.State.ready out.1) <$> simulateQ (adapter limit) (source word) := by
  have hw : Within limit (4 + 2 * word.length + 4 * limit)
      (BitOracleMachine.run code 4 (initial word)) := by
    rw [BitOracleCanary.run_source]
    exact within limit word
  simpa only [BitOracleCanary.run_source] using
    BitOracleLoopBounded.run_source code 4 limit (4 + 2 * word.length + 4 * limit) (initial word) hw

/-- The same common clock preserves complete handler effects and output law. -/
theorem run_handler {M : Type → Type} [Monad M] [LawfulMonad M]
    (limit : Nat) (word : List Bool) (handler : QueryImpl (spec limit) M) :
    simulateQ handler (simulateQ (adapter limit)
      (BitOracleLoop.run code (11 * (4 + 2 * word.length + 4 * limit))
        (.ready (initial word)))) =
      (fun out => BitOracleLoop.State.ready out.1) <$>
        simulateQ handler (simulateQ (adapter limit) (source word)) := by
  rw [run, simulateQ_map]

end ExplainableCrypto.Helios.Computational.BitOracleBoundedCanary
