import ExplainableCrypto.Helios.Computational.CoinScalarMachine
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Literal whole-machine controls and a counterexample to live-return padding. -/
namespace ExplainableCrypto.Helios.Computational.CoinScalarMachineControls
open OracleComp OracleSpec BitOracleMachine CoinScalarMachine

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r answers =>
  match r with
  | .coin => (answers.headD false,answers.tail)
  | .hash request => (request,answers)

private def observe (fuel : Nat) (width : List Bool) (q : Nat) (answers : List Bool) :=
  let out := (simulateQ handler (run code fuel (start width q))).run answers
  (out.1.1.l,out.1.1.var,
    [out.1.1.stk 0,out.1.1.stk 1,out.1.1.stk 2,out.1.1.stk 3,
      out.1.1.stk 4,out.1.1.stk 5,out.1.1.stk 6,out.1.1.stk 7],out.2)

theorem sampled_two :
    observe 80 [false,true] 3 [false,true,true,false] =
    (none,2,[[],[true,true],[],[],[],[true,true,false,false,true],[],[]],[true,false]) := by
  decide +kernel

theorem sampled_one :
    observe 140 [true,true,true] 5 [false,true,true,false,true] =
    (none,2,[[],[true,false,true],[],[],[],[true,false,true],[],[]],[false,true]) := by
  decide +kernel

theorem empty_zero :
    observe 8 [] 1 [true,false] =
    (none,2,[[],[true],[],[],[],[false],[],[]],[true,false]) := by
  decide +kernel

/-- The old terminal step is an actual jump to the writer, retaining every stack. -/
theorem live_return :
    observe 5 [] 1 [true,false] =
    (some 25,0,[[],[true],[],[],[],[],[],[]],[true,false]) := by
  decide +kernel

/-- Padding a final halted configuration is harmless and consumes no future coin. -/
theorem final_padding :
    observe 40 [] 1 [true,false] = observe 8 [] 1 [true,false] := by
  decide +kernel

private def source : Code 1 1 1 := fun _ => .compute .halt
private def liveCode : Code 1 2 1 := ![.compute (.goto (fun _ => 1)),.coin 0 1]
private def initial : BitOracleMachine.Config 1 1 1 := ⟨some 0,0,fun _ => []⟩
private def labels (_ : Fin 1) : Fin 2 := 0
private def staged : OracleComp spec (BitOracleMachine.Config 1 2 1 × Nat) := do
  let first ← run source 2 initial
  let last ← run liveCode 1 (BitOracleReturnLink.embed labels (some 1) first.1)
  pure (last.1,first.2+last.2)
private def view (computation : OracleComp spec (BitOracleMachine.Config 1 2 1 × Nat)) :=
  let out := (simulateQ handler computation).run [true,false,true]
  (out.1.1.l,out.1.1.stk 0,out.2)

/-- Without final continuation termination, redirected padding adds another query.
This refutes dropping the linker's continuation-halt premise. -/
theorem live_padding_fails :
    view (run liveCode 3 (BitOracleReturnLink.embed labels (some 1) initial)) ≠ view staged := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.CoinScalarMachineControls
