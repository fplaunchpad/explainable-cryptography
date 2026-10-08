import ExplainableCrypto.Helios.Computational.BitOracleInitialInput
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Literal raw-input fixtures, independent of canonical packing. -/
namespace ExplainableCrypto.Helios.Computational.OracleInitialInputControls
open Turing OracleComp OracleSpec BitOracleInitialInput
open OracleTapeOutput (WorkTape wordTape)
open OracleTapeDispatch (readWord)

private def code : BitOracleMachine.Code 2 1 1 := fun _ => .hash 1 0 0
private def handler : QueryImpl BitOracleMachine.spec (StateT (List (List Bool)) Id) :=
  fun request log => match request with
    | .coin => (false, log)
    | .hash word => (word, log ++ [word])

private def column (port : BitOraclePortTransfer.Ports 2)
    (tape : WorkTape (BitOraclePortTransfer.Ports 2)) : List Bool :=
  (readWord (tape.map ⟨fun cell => cell.2 port, rfl⟩)).reverse

private structure View where
  label : Option Nat
  bottom : Bool
  first : List Bool
  second : List Bool
  privateInput : List Bool
  privateScratch : List Bool
  query : List Bool
  input : List Bool
  deriving DecidableEq

private def view (fuel : Nat) (word : List Bool) : Option View × List (List Bool) :=
  let out := (simulateQ handler (run code 1 (some 0) 0 fuel (initial word))).run []
  (match out.1 with
    | .running (.ready label _ tapes) => some ⟨label.map Fin.val, tapes.work.head.1,
        column (.inl 0) tapes.work, column (.inl 1) tapes.work,
        column (.inr false) tapes.work, column (.inr true) tapes.work,
        readWord tapes.query, readWord tapes.answer⟩
    | _ => none, out.2)

/-- Empty input still writes the bottom marker and completes startup. -/
theorem empty_input : view 8 [] = (some ⟨some 0, true, [], [], [], [], [], []⟩, []) := by
  decide +kernel

/-- Input order and the selected nonzero port are pinned by a literal fixture. -/
theorem nonpalindromic_input : view 20 [false, true, true] =
    (some ⟨some 0, true, [], [false, true, true], [], [], [], [false, true, true]⟩, []) := by
  decide +kernel

/-- Startup cannot be replaced by a free canonical load at clock zero. -/
theorem zero_clock : view 0 [false, true, true] = (none, []) := by rfl

/-- A proper loading prefix has not yet handed control to the program. -/
theorem before_handoff : view 19 [false, true, true] = (none, []) := by decide +kernel

/-- Actual execution continues from the loaded tape and issues its first hash
on the original raw input, without an input-side oracle event. -/
theorem loaded_request :
    let out := (simulateQ handler (run code 1 (some 0) 0 256
      (initial [false, true, true]))).run []
    out.2.head? = some [false, true, true] := by decide +kernel

/-- Even an already halted label pays for input loading and retains the input. -/
theorem halted_entry :
    ∃ used ≤ 20, run code 1 none 0 used (initial [false, true, true]) =
      pure (.running (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready
        (source 1 none 0 [false, true, true]) (wordTape []) (wordTape [false, true, true])))) :=
  load code 1 none 0 [false, true, true]

end ExplainableCrypto.Helios.Computational.OracleInitialInputControls
