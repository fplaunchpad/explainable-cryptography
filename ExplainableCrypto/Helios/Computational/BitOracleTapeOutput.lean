import ExplainableCrypto.Helios.Computational.OracleTapeOutput
import ExplainableCrypto.Helios.Computational.BitOracleTapeCost

/-! Connect physical query export to the completed actual request preparation.
The exported native tape contains exactly the original raw request. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeOutput
open Turing TM2TapeRuns BitOraclePortTransfer OracleTapeOutput

/-- Request preparation followed by head-local physical export. Both execution
results are derived from the actual caller state; no presentation is assumed. -/
theorem request_run {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request : Fin s) (next : Fin l) (oldPort previousQuery : List Bool) :
    let src := requestStart cfg request next oldPort
    let B := oldPort.length + 2 * (cfg.stk request).length + 4
    ∃ used ≤ B * (6 * height src.stk + 18 * B + 7),
      let out := (TM2TapeCost.tick (requestProgram request))^[used] (pack src)
      out = pack {requestStart cfg request next (cfg.stk request) with l := none} ∧
      (step (.inr false : Ports s))^[previousQuery.length + 2 * (cfg.stk request).length + 3]
          ⟨.clear, out.Tape, wordTape previousQuery⟩ =
        ⟨.done, out.Tape, wordTape (cfg.stk request)⟩ := by
  dsimp only
  obtain ⟨used, hu, ht⟩ := BitOracleTapeCost.request_run cfg request next oldPort
  refine ⟨used, hu, ht, ?_⟩
  rw [ht]
  exact OracleTapeOutput.run_replacing
    {requestStart cfg request next (cfg.stk request) with l := none} (.inr false) previousQuery

end ExplainableCrypto.Helios.Computational.BitOracleTapeOutput
