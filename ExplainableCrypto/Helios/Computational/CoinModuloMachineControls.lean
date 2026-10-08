import ExplainableCrypto.Helios.Computational.CoinModuloMachine
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Full-state controls for actual coin-to-remainder execution. Numeric results
are supplied independently; leftover coins expose unwanted return/restart queries. -/
namespace ExplainableCrypto.Helios.Computational.CoinModuloMachineControls
open OracleComp OracleSpec BitOracleMachine CoinModuloMachine

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r answers =>
  match r with
  | .coin => (answers.headD false, answers.tail)
  | .hash request => (request, answers)

private def observe (fuel : Nat) (width : List Bool) (q : Nat) (answers : List Bool) :=
  let out := (simulateQ handler
    (run code fuel (loading (some 15) width [] [] [] q.bits))).run answers
  (out.1.1.l, out.1.1.var,
    [out.1.1.stk 0,out.1.1.stk 1,out.1.1.stk 2,out.1.1.stk 3,
      out.1.1.stk 4,out.1.1.stk 5,out.1.1.stk 6,out.1.1.stk 7],out.2)

/-- Six modulo five is one; all scratch clears and the unused coins remain. -/
theorem input_order :
    observe 128 [true,true,true] 5 [false,true,true,false,true] =
      (none,0,[[true],[true,false,true],[],[],[],[],[],[]],[false,true]) := by
  decide +kernel

/-- Two modulo three retains its nonpalindromic two-digit representation. -/
theorem output_order :
    observe 71 [false,true] 3 [false,true,true,false] =
      (none,0,[[false,true],[true,true],[],[],[],[],[],[]],[true,false]) := by
  decide +kernel

/-- Unit modulus yields canonical zero without rejecting or querying again. -/
theorem modulus_one :
    observe 80 [true,true,true] 1 [true,false,true,true] =
      (none,0,[[],[true],[],[],[],[],[],[]],[true]) := by
  decide +kernel

/-- Empty width executes loader, division and halt without consuming a coin. -/
theorem empty_input :
    observe 5 [] 3 [true,false] =
      (none,0,[[],[true,true],[],[],[],[],[],[]],[true,false]) := by
  decide +kernel

/-- The actual call boundary retains the raw chronological word on port six. -/
theorem live_handoff :
    observe 14 [true,true,true] 5 [false,true,true,false] =
      (some 11,0,[[],[true,false,true],[],[],[],[],[false,true,true],[]],[false]) := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.CoinModuloMachineControls
