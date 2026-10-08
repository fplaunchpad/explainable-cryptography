import ExplainableCrypto.Helios.Computational.CoinWordLoader
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Literal response streams independently pin ordering, exhaustion and charge.
The handler is a deterministic test fixture, not a cryptographic assumption. -/
namespace ExplainableCrypto.Helios.Computational.CoinWordLoaderControls
open OracleComp OracleSpec BitOracleMachine CoinWordLoader

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r answers =>
  match r with
  | .coin => (answers.headD false, answers.tail)
  | .hash request => (request, answers)

private def observe (fuel : Nat) (width modulus answers : List Bool) :=
  let result := (simulateQ handler
    (run code fuel (state (some 0) width [] [] [] modulus))).run answers
  (result.1.1.l, result.1.1.var,
    [result.1.1.stk 0, result.1.1.stk 1, result.1.1.stk 2,
      result.1.1.stk 3, result.1.1.stk 4], result.1.2, result.2)

/-- Chronological low-bit-first output and complete scratch cleanup. -/
theorem input_order :
    observe 10 [true,true] [true,false,true] [false,true,false] =
      (none, 0, [[],[],[],[false,true],[true,false,true]], 39, [false]) := by
  decide +kernel

/-- Width tokens are consumed by presence; their Boolean payload is irrelevant.
The caller's arbitrary modulus word is retained, including padding. -/
theorem width_and_frame :
    observe 14 [false,true,false] [false,true,false,false] [true,false,false,true] =
      (none, 0, [[],[],[],[true,false,false],[false,true,false,false]], 54, [true]) := by
  decide +kernel

/-- Zero width halts without querying and retains the whole response stream. -/
theorem zero_width :
    observe 2 [] [true] [true,false] =
      (none, 0, [[],[],[],[],[true]], 9, [true,false]) := by
  decide +kernel

/-- Refute the initially proposed 15*w+8 charge: even zero width costs nine. -/
theorem charge_eight_fails :
    (observe 2 [] [] []).2.2.2.1 > 8 := by
  decide +kernel

/-- Two steps consume one coin and leave a live response awaiting collection. -/
theorem live_response :
    observe 2 [true,true] [false,true] [false,true,true] =
      (some 2, 0, [[true],[false],[],[],[false,true]], 6, [true,true]) := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.CoinWordLoaderControls
