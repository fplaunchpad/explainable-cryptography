import ExplainableCrypto.Helios.Computational.ScalarWriteCode
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Independent literal controls for scalar serialization and its sampler handoff. -/
namespace ExplainableCrypto.Helios.Computational.ScalarWriteCodeControls
open OracleComp OracleSpec BitOracleMachine ScalarWriteCode

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r answers =>
  match r with
  | .coin => (answers.headD false,answers.tail)
  | .hash request => (request,answers)

private def observe (width : List Bool) (q : Nat) (answers : List Bool) :=
  let out := (simulateQ handler (sampleWord width q)).run answers
  (out.1.1.l,out.1.1.var,
    [out.1.1.stk 0,out.1.1.stk 1,out.1.1.stk 2,out.1.1.stk 3,
      out.1.1.stk 4,out.1.1.stk 5,out.1.1.stk 6,out.1.1.stk 7],out.2)

/-- Two has digits 01 and prefix 11001; every unrelated port is retained. -/
theorem digits_and_frame :
    (TM2ReturnLink.tick program)^[9]
      (start [false,true] [true,true] [true,false] [false,true] [true]) =
    result [true,true,false,false,true,true,false] [true,true] [false,true] [true] := by
  exact run_digits 2 [true,true] [true,false] [false,true] [true]

/-- A nearby wrong-endian prefix fails on the same scalar. -/
theorem reversed_digits_fail :
    (TM2ReturnLink.tick program)^[9] (start [false,true] [true,true] [] [] []) ≠
    result [true,true,false,true,false] [true,true] [] [] := by
  intro h
  have hx := congrArg (fun cfg : ScalarWriteCode.Config => cfg.stk 5) h
  have good : (TM2ReturnLink.tick program)^[9] (start [false,true] [true,true] [] [] []) =
      result [true,true,false,false,true] [true,true] [] [] := run_digits 2 [true,true] [] [] []
  rw [good] at hx
  change ([true,true,false,false,true] : List Bool) = [true,true,false,true,false] at hx
  simp at hx

/-- Zero consumes three transitions and emits a delimiter. -/
theorem zero_delimiter :
    (TM2ReturnLink.tick program)^[3] (start [] [true] [] [] []) =
    result [false] [true] [] [] := by
  exact run_digits 0 [true] [] [] []

theorem omitted_zero_fails :
    (TM2ReturnLink.tick program)^[3] (start [] [true] [] [] []) ≠
    result [] [true] [] [] := by
  intro h
  have hx := congrArg (fun cfg : ScalarWriteCode.Config => cfg.stk 5) h
  rw [zero_delimiter] at hx
  change ([false] : List Bool) = [] at hx
  simp at hx

/-- Actual two-phase execution consumes precisely the two supplied scalar coins. -/
theorem sampled_two :
    observe [false,true] 3 [false,true,true,false] =
    (none,2,[[],[true,true],[],[],[],[true,true,false,false,true],[],[]],[true,false]) := by
  decide +kernel

/-- Empty coin width still writes zero, preserving all future oracle answers. -/
theorem sampled_zero :
    observe [] 1 [true,false] =
    (none,2,[[],[true],[],[],[],[false],[],[]],[true,false]) := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.ScalarWriteCodeControls
