import ExplainableCrypto.Helios.Computational.OracleTapeInput
import ExplainableCrypto.Helios.Computational.BitOracleTapeCost

/-! Derive the physical answer input to the actual consuming response program. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeInput
open Turing TM2TapeRuns BitOraclePortTransfer OracleTapeOutput

/-- Loading the native answer into the completed request tape produces the
actual response program's work tape, including every caller/scratch column. -/
theorem load_request {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (oldPort answer : List Bool) :
    let src : BitOraclePortTransfer.Config s l m := {requestStart cfg request next oldPort with l := none}
    (OracleTapeInput.step (.inr false : Ports s))^[3 * oldPort.length + 4 * answer.length + 6]
        ⟨.seekWork, (pack src).Tape, wordTape answer⟩ =
      ⟨.done, (pack (start cfg destination next answer)).Tape, wordTape answer⟩ := by
  dsimp only
  have hr := OracleTapeInput.run_packed
    ({requestStart cfg request next oldPort with l := none} : BitOraclePortTransfer.Config s l m)
    (.inr false) answer
  have he := congrArg TM2.Cfg.stk (delivery_start cfg request destination next answer oldPort)
  change Function.update (requestStart cfg request next oldPort).stk (.inr false) answer =
    (start cfg destination next answer).stk at he
  have hw : (pack ({{requestStart cfg request next oldPort with l := none} with
        stk := Function.update (requestStart cfg request next oldPort).stk (.inr false) answer} : BitOraclePortTransfer.Config s l m)).Tape =
      (pack (start cfg destination next answer)).Tape := by
    change Tape.mk' ∅ (TM2to1.addBottom (columns (Function.update
      (requestStart cfg request next oldPort).stk (.inr false) answer))) =
      Tape.mk' ∅ (TM2to1.addBottom (columns (start cfg destination next answer).stk))
    rw [he]
  simpa only [hw, (request_start cfg request request next oldPort).2.1] using hr

/-- Physical native loading followed by the actual full response transfer.
The resumed caller and empty private workspace follow from both executions. -/
theorem response_run {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (oldPort answer : List Bool) :
    let incoming : BitOraclePortTransfer.Config s l m := {requestStart cfg request next oldPort with l := none}
    let ready := start cfg destination next answer
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ used ≤ B * (6 * height ready.stk + 18 * B + 7),
      ∃ out : BitOraclePortTransfer.Config s l m,
        (OracleTapeInput.step (.inr false : Ports s))^[3 * oldPort.length + 4 * answer.length + 6]
            ⟨.seekWork, (pack incoming).Tape, wordTape answer⟩ =
          ⟨.done, (pack ready).Tape, wordTape answer⟩ ∧
        (TM2TapeCost.tick (program destination))^[used] (pack ready) = pack out ∧
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] := by
  dsimp only
  obtain ⟨used, hu, out, ht, hr⟩ := BitOracleTapeCost.response_run cfg destination next answer
  exact ⟨used, hu, out, load_request cfg request destination next oldPort answer, ht, hr⟩

end ExplainableCrypto.Helios.Computational.BitOracleTapeInput
