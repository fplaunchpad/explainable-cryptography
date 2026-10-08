import ExplainableCrypto.Helios.Computational.ScalarDifferenceMachineRun

/-! Independent literal endpoints and actual instruction mutations for scalar
operand preparation. These bounded kernel reductions complement the general run. -/
namespace ExplainableCrypto.Helios.Computational.ScalarDifferenceMachineControls
open Turing.TM2 ScalarDifferenceMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private def observe (cfg : Config) := (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)

/-- The q=1 endpoint has three zero scalar prefixes and no residual work. -/
theorem modulus_one_zero_full_state :
    observe (tick^[clock 1] (start [true] [false] [false])) =
      (none,2,[[true],[false],[false],[false],[],[],[],[],[],[]]) := by decide +kernel

/-- In ZMod3, 1-2 is2: natural monus and reversed operands both disagree. -/
theorem underflow_full_state :
    observe (tick^[clock 3]
      (start [true,true] [true,false,true] [true,true,false,false,true])) =
      (none,2,[[true,true],[true,false,true],[true,true,false,false,true],
        [true,true,false,false,true],[],[],[],[],[],[]]) := by decide +kernel

/-- A zero second operand is allowed and leaves the first scalar unchanged. -/
theorem second_zero_full_state :
    observe (tick^[clock 3] (start [true,true] [true,false,true] [false])) =
      (none,2,[[true,true],[true,false,true],[false],[true,false,true],[],[],[],[],[],[]]) := by decide +kernel

/-- The same instruction changes used by the independent gate: omit the e-digit
clear loop, or damage the preserved c-prefix at the final successful return. -/
private def mutated (m : Nat) (l : Fin size) :=
  if m == 3 && l == 4 then .load (fun _ => 0) (.goto (fun _ => writerEntry))
  else if m == 4 && l == 5 then .push 1 (fun _ => false) (program l)
  else program l

private def mutantOutput (m : Nat) :=
  observe ((TM2ReturnLink.tick (mutated m))^[clock 3]
    (start [true,true] [true,false,true] [true,true,false,false,true]))

/-- Skipping cleanup returns the right scalar but leaves the parsed e word in
scratch port4; the full-state contract detects this defect. -/
theorem omitted_cleanup_full_state :
    mutantOutput 3 =
      (none,2,[[true,true],[true,false,true],[true,true,false,false,true],
        [true,true,false,false,true],[false,true],[],[],[],[],[]]) := by decide +kernel

theorem omitted_cleanup_is_detected :
    mutantOutput 3 ≠
      (none,2,[[true,true],[true,false,true],[true,true,false,false,true],
        [true,true,false,false,true],[],[],[],[],[],[]]) := by
  rw [omitted_cleanup_full_state]
  decide +kernel

/-- Correct arithmetic alone does not justify preservation of the input prefix. -/
theorem corrupted_prefix_full_state :
    mutantOutput 4 =
      (none,2,[[true,true],[false,true,false,true],[true,true,false,false,true],
        [true,true,false,false,true],[],[],[],[],[],[]]) := by decide +kernel

theorem corrupted_prefix_is_detected :
    mutantOutput 4 ≠
      (none,2,[[true,true],[true,false,true],[true,true,false,false,true],
        [true,true,false,false,true],[],[],[],[],[],[]]) := by
  rw [corrupted_prefix_full_state]
  decide +kernel

#print axioms modulus_one_zero_full_state
#print axioms underflow_full_state
#print axioms second_zero_full_state
#print axioms omitted_cleanup_full_state
#print axioms omitted_cleanup_is_detected
#print axioms corrupted_prefix_full_state
#print axioms corrupted_prefix_is_detected
end ExplainableCrypto.Helios.Computational.ScalarDifferenceMachineControls
