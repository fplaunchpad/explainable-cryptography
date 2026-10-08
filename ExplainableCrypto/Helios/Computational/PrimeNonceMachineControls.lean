import ExplainableCrypto.Helios.Computational.PrimeNonceMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeNonceMachineControls
open PrimeNonceMachine
set_option maxRecDepth 8192
def observe (cfg : Config) := (cfg.l,cfg.var,List.ofFn cfg.stk)

/-- q=2 has only sampled index zero; the actual continuation returns nonce one. -/
theorem zero_to_one :
    observe ((TM2ReturnLink.tick program)^[22]
      (start [false] ![[true],[false],[true,false]])) =
    observe (result [true,false,true] ![[true],[false],[true,false]]) := by decide +kernel

/-- Carry changes 3 to 4, including the canonical prefix length. -/
theorem carry_three_to_four :
    observe ((TM2ReturnLink.tick program)^[44]
      (start [true,true,false,true,true,false,true] ![[false],[true],[]])) =
    observe (result [true,true,true,false,false,false,true,false,true] ![[false],[true],[]]) := by
  decide +kernel

/-- Nonzero nonce generation cannot be the identity on the sampled index. -/
theorem zero_not_identity :
    ((TM2ReturnLink.tick program)^[22]
      (start [false] ![[true],[false],[true,false]])).stk 4 ≠ [false] := by
  decide +kernel

/-- Omitted increment is detected on the smallest index. -/
private def bypassIncrement (l : Fin 26) :=
  if l == prepLabel 10 then program (prepLabel 12) else program l

theorem bypass_increment_counterexample :
    ((TM2ReturnLink.tick bypassIncrement)^[22] (start [false] (fun _ => []))).stk 4 =
      [false] := by decide +kernel

private def skipClear (l : Fin 26) :=
  if l == 16 then Turing.TM2.Stmt.goto (fun _ : Fin 3 => writeLabel 5) else program l

/-- The old width marker would corrupt the new prefix. -/
theorem skip_clear_counterexample :
    ((TM2ReturnLink.tick skipClear)^[22] (start [false] (fun _ => []))).stk 4 =
      [true,true,false,true] := by decide +kernel

private def corruptFrame (l : Fin 26) :=
  if l == 25 then Turing.TM2.Stmt.push (5 : Fin 8) (fun _ : Fin 3 => false)
    Turing.TM2.Stmt.halt else program l

theorem corrupt_frame_counterexample :
    ((TM2ReturnLink.tick corruptFrame)^[22] (start [false] (fun _ => []))).stk 5 =
      [false] := by decide +kernel

#print axioms zero_to_one
#print axioms carry_three_to_four
#print axioms zero_not_identity
#print axioms bypass_increment_counterexample
#print axioms skip_clear_counterexample
#print axioms corrupt_frame_counterexample
end ExplainableCrypto.Helios.Computational.PrimeNonceMachineControls
