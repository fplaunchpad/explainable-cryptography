import ExplainableCrypto.Helios.Computational.BitTapeStart

/-! Literal conversion, linked source and actual physical-startup controls. -/
namespace ExplainableCrypto.Helios.Computational.BitTapeInputControls
open Turing OracleComp OracleSpec

private def machine : TM0.Machine BitTapeCoverage.Cell (Fin 1) := fun _ c => match c with
  | some false => some (0, .write (some true))
  | _ => none

private def code : BitOracleMachine.Code 2 5 3 := fun q => .compute (BitTapeStart.program machine 0 q)

private def handler : QueryImpl BitOracleMachine.spec Id := fun q => match q with
  | .coin => false
  | .hash _ => []

private def view (c : BitOracleMachine.Config 2 5 3) : Option Nat × Nat × List Bool × List Bool :=
  (c.l.map Fin.val, c.var.val, c.stk 0, c.stk 1)

/-- Exact converter output, with the first false bit retained as a data cell. -/
theorem conversion :
    let c := (TM2ReturnLink.tick BitTapeInput.program)^[9] (BitTapeInput.initial [false, true, true])
    (c.l.map Fin.val, c.var.val, c.stk 0, c.stk 1) =
      (none, 1, [], [true, true, true, true]) := by decide +kernel

/-- Before head extraction the complete tagged word is still on the right. -/
theorem conversion_prefix :
    let c := (TM2ReturnLink.tick BitTapeInput.program)^[8] (BitTapeInput.initial [false, true, true])
    (c.l.map Fin.val, c.var.val, c.stk 0, c.stk 1) =
      (some 2, 0, [], [true, false, true, true, true, true]) := by decide +kernel

/-- Actual linked source execution changes the native false head to true. -/
theorem linked_source :
    view (simulateQ handler (BitOracleMachine.run code 12
      (BitTapeStart.initial 0 [false, true, true]))).1 =
      (none, 2, [], [true, true, true, true]) := by decide +kernel

/-- The native return reaches its separate stop label; it does not restart. -/
theorem native_return :
    view (simulateQ handler (BitOracleMachine.run code 11
      (BitTapeStart.initial 0 [false, true, true]))).1 =
      (some 3, 2, [], [true, true, true, true]) := by decide +kernel

/-- Empty input produces a blank head and still executes conversion and halt. -/
theorem empty_source :
    view (simulateQ handler (BitOracleMachine.run code 5 (BitTapeStart.initial 0 []))).1 =
      (none, 0, [], []) := by decide +kernel

/-- Execute actual physical loading and primitive steps, not the source clock
formula. Full caller data agrees with the independent linked-source fixture. -/
theorem physical_literal :
    (BitOracleInitialInput.observe (simulateQ handler
      (BitOracleInitialInput.run code 1 (some 0) 0 1024
        (BitOracleInitialInput.initial [false, true, true])))).map view =
      some (none, 2, [], [true, true, true, true]) := by decide +kernel

/-- The machine itself supplies a halt bound for every raw input word. -/
theorem native_halts (word : List Bool) :
    ((BitTapeCoverage.tick machine)^[2] (BitTapeInput.native (some 0) word)).label = none := by
  cases word with
  | nil => rfl
  | cons bit rest => cases bit <;> rfl

end ExplainableCrypto.Helios.Computational.BitTapeInputControls
