import ExplainableCrypto.Helios.Computational.BitTapeCoverage

/-! Independently specified tape fixtures distinguish blank/data cells,
head motion and premature halting in actual source execution. -/
namespace ExplainableCrypto.Helios.Computational.BitTapeCoverageControls
open Turing OracleComp OracleSpec BitTapeCoverage

private def machine : TM0.Machine Cell (Fin 6) := fun q _ => match q.val with
  | 0 => some (1, .write (some false))
  | 1 => some (2, .move .left)
  | 2 => some (3, .write (some true))
  | 3 => some (4, .move .right)
  | 4 => some (5, .move .right)
  | _ => none

private def handler : QueryImpl BitOracleMachine.spec Id := fun q => match q with
  | .coin => false
  | .hash _ => []

private def initial : Config 6 := ⟨some 0, none, [], []⟩

private def view (fuel : Nat) : Option Nat × Nat × List Bool × List Bool :=
  let out := simulateQ handler
    (BitOracleMachine.run (fun q => .compute (program machine q)) fuel (present initial))
  (out.1.l.map Fin.val, out.1.var.val, out.1.stk 0, out.1.stk 1)

/-- Write at the origin and to its left, return, then move right into blank.
Nearest-left cells are false then true; each has its explicit present tag. -/
theorem full_run : view 6 = (none, 0, [true, false, true, true], []) := by decide +kernel

/-- Correct tape data does not imply that the machine has already halted. -/
theorem before_halt : view 5 = (some 5, 0, [true, false, true, true], []) := by decide +kernel

/-- Direct pinned TM0 execution independently gives the same relative tape. -/
theorem native_run :
    let out := (fun c => (TM0.step machine c).getD c)^[6]
      (⟨0, default⟩ : TM0.Cfg Cell (Fin 6))
    (out.q.val, out.Tape.head, out.Tape.nth (-1), out.Tape.nth (-2), out.Tape.nth 1) =
      (5, none, some false, some true, none) := by decide +kernel

/-- Moving left off empty storage reads blank and stores a blank on the right. -/
theorem empty_left :
    let out := simulateQ handler (BitOracleMachine.run
      (fun q => .compute (program machine q)) 1 (present (⟨some 1, none, [], []⟩ : Config 6)))
    (out.1.l.map Fin.val, out.1.var.val, out.1.stk 0, out.1.stk 1) =
      (some 2, 0, [], [false, false]) := by decide +kernel

private def branchMachine : TM0.Machine Cell (Fin 1) := fun _ c => match c with
  | none => some (0, .write (some false))
  | some _ => none

/-- A machine can distinguish blank from false; conflating them loses a step
and the write. This run executes the actual source head-selection branches. -/
theorem blank_is_not_false :
    let out := simulateQ handler (BitOracleMachine.run
      (fun q => .compute (program branchMachine q)) 2
      (present (⟨some 0, none, [], []⟩ : Config 1)))
    (out.1.l.map Fin.val, out.1.var.val, out.1.stk 0, out.1.stk 1) =
      (none, 1, [], []) := by decide +kernel

/-- The complete program's cost is derived, not a caller efficiency certificate. -/
theorem run_cost : ∃ charge ≤ 42,
    BitOracleMachine.run (fun q => .compute (program machine q)) 6 (present initial) =
      pure (present ((tick machine)^[6] initial), charge) := charged_run machine 6 initial

end ExplainableCrypto.Helios.Computational.BitTapeCoverageControls
