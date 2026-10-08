import ExplainableCrypto.Helios.Computational.NativeOracleTape
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Native reference controls for independent tape heads and complete private
frames. Expected cells and event logs are specified independently. -/
namespace ExplainableCrypto.Helios.Computational.NativeOracleTapeControls
open Turing OracleComp OracleSpec NativeOracleTape
open OracleTapeOutput (wordTape)

private def handler (coin : Bool) : QueryImpl BitOracleMachine.spec (StateT (List BitOracleMachine.Request) Id) :=
  fun q log => match q with
    | .coin => (coin, log ++ [q])
    | .hash _ => ([false, true], log ++ [q])

private def config : Config 3 :=
  ⟨some 0,
    Tape.mk' (ListBlank.mk [some true]) (ListBlank.mk [some false, some true]),
    Tape.mk' (ListBlank.mk [some true]) (ListBlank.mk [some false, none, some true]),
    (wordTape [true, true, true]).move .right⟩

private def hashCode : Code 3 := fun _ _ => .oracle .hash 2

private structure View where
  label : Option Nat
  workHead : Cell
  workBefore : Cell
  workAfter : Cell
  queryHead : Cell
  queryBefore : Cell
  queryAfterTwo : Cell
  answerHead : Cell
  answerBefore : Cell
  answerAfter : Cell
  answerAfterTwo : Cell
  deriving DecidableEq

private def view (c : Config 3) : View :=
  ⟨c.label.map Fin.val, c.work.head, c.work.nth (-1), c.work.nth 1,
    c.query.head, c.query.nth (-1), c.query.nth 2,
    c.answer.head, c.answer.nth (-1), c.answer.nth 1, c.answer.nth 2⟩

private def observe (code : Code 3) (fuel : Nat) (coin : Bool := true) :
    View × List BitOracleMachine.Request :=
  let out := (simulateQ (handler coin) (run code fuel config)).run []
  (view out.1, out.2)

/-- Query reading stops at the embedded blank, while all its other cells and
private work survive; old answer cells and its displaced head are replaced. -/
theorem hash_frame : observe hashCode 1 =
    (⟨some 2, some false, some true, some true, some false, some true, some true,
      some false, none, some true, none⟩, [.hash [false]]) := by decide +kernel

/-- Identical visible word prefixes do not justify aliasing work and answer:
the actual private cell to the left is preserved only on the work tape. -/
theorem work_answer_alias_fails :
    let out := ((simulateQ (handler true) (run hashCode 1 config)).run []).1
    out.work.nth (-1) ≠ out.answer.nth (-1) := by decide +kernel

private def moveQueryCode : Code 3 := fun q _ => if q = 0 then
  .local 1 ![none, some (.move .left), none] else .oracle .hash 2

/-- Native query heads may move left; the next request includes that cell. -/
theorem moved_query : observe moveQueryCode 2 =
    (⟨some 2, some false, some true, some true, some true, none, none,
      some false, none, some true, none⟩, [.hash [true, false]]) := by decide +kernel

private def coinCode : Code 3 := fun q h =>
  if q = 0 then .oracle .coin 1
  else if q = 1 then
    .local 2 ![some (.write (some (h 2 == some true))), none, some (.move .right)]
  else .halt

/-- The received coin drives a later work write and answer-head movement. -/
theorem true_answer : observe coinCode 3 =
    (⟨none, some true, some true, some true, some false, some true, some true,
      none, some true, none, none⟩, [.coin]) := by decide +kernel

/-- The false branch has a different work result and retained answer cell. -/
theorem false_answer : observe coinCode 3 false =
    (⟨none, some false, some true, some true, some false, some true, some true,
      none, some false, none, none⟩, [.coin]) := by decide +kernel

/-- Halting freezes the complete reference state without adding oracle calls. -/
theorem halted_frame : run hashCode 10 {config with label := none} =
    pure {config with label := none} := run_halted hashCode 10 _ rfl

end ExplainableCrypto.Helios.Computational.NativeOracleTapeControls
