import ExplainableCrypto.Helios.Computational.BinaryModuloMachine
import ExplainableCrypto.Helios.Computational.BitOracleCanary
import ExplainableCrypto.Helios.Computational.TM2FiniteCoordinates

/-! Executable finite coordinates for the existing division program. This
adapter changes only finite stack, label and local-memory names. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModuloCode
open Turing.TM2
namespace Source
abbrev Stack := BinaryModuloMachine.Stack
abbrev Label := BinaryModuloMachine.Label
end Source

/-- Remainder, modulus, difference, left/right archive, output, raw, pending. -/
def ports : Source.Stack ≃ Fin 8 where
  toFun
    | .inl .left => 0 | .inl .right => 1 | .inl .diff => 2
    | .inl .savedLeft => 3 | .inl .savedRight => 4 | .inl .out => 5
    | .inr false => 6 | .inr true => 7
  invFun := ![.inl .left, .inl .right, .inl .diff, .inl .savedLeft,
    .inl .savedRight, .inl .out, .inr false, .inr true]
  left_inv s := by cases s with
    | inl s => cases s <;> rfl
    | inr b => cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Eleven subtraction labels followed by the four division-driver labels. -/
def labels : Source.Label ≃ Fin 15 where
  toFun
    | .call (.scan false) => 0 | .call (.scan true) => 1
    | .call (.restoreRight false) => 2 | .call (.restoreRight true) => 3
    | .call (.shift false) => 4 | .call (.shift true) => 5
    | .call .clearDiff => 6 | .call .restoreLeft => 7 | .call .clearLeft => 8
    | .call .trim => 9 | .call .reverse => 10
    | .reverseInput => 11 | .read => 12 | .toTemp => 13 | .toLeft => 14
  invFun := ![.call (.scan false), .call (.scan true), .call (.restoreRight false),
    .call (.restoreRight true), .call (.shift false), .call (.shift true),
    .call .clearDiff, .call .restoreLeft, .call .clearLeft, .call .trim,
    .call .reverse, .reverseInput, .read, .toTemp, .toLeft]
  left_inv l := by
    cases l with
    | call l => cases l <;> first | rfl | (rename_i b; cases b <;> rfl)
    | reverseInput | read | toTemp | toLeft => rfl
  right_inv i := by fin_cases i <;> rfl

def memory : Option Bool ≃ Fin 3 where
  toFun | none => 0 | some false => 1 | some true => 2
  invFun := ![none, some false, some true]
  left_inv v := by cases v with
    | none => rfl
    | some b => cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def present : BinaryModuloMachine.Config → BitOracleMachine.Config 8 15 3 :=
  TM2FiniteCoordinates.present ports labels memory

def program : Fin 15 → Stmt (fun _ : Fin 8 => Bool) (Fin 15) (Fin 3) :=
  TM2FiniteCoordinates.program ports labels memory BinaryModuloMachine.program

/-- All configurations, including intermediate scratch contents, translate exactly. -/
theorem tick (cfg : BinaryModuloMachine.Config) :
    TM2ReturnLink.tick program (present cfg) = present (BinaryModuloMachine.tick cfg) :=
  TM2FiniteCoordinates.tick ports labels memory BinaryModuloMachine.program cfg

/-- Entire original executions retain their transition count and full frame. -/
theorem run (fuel : Nat) (cfg : BinaryModuloMachine.Config) :
    (TM2ReturnLink.tick program)^[fuel] (present cfg) =
      present (BinaryModuloMachine.tick^[fuel] cfg) :=
  TM2FiniteCoordinates.run ports labels memory BinaryModuloMachine.program fuel cfg

/-- The translated program has a fixed local source-operation bound. -/
theorem local_cost (label : Fin 15) : BitOracleMachine.localCost (program label) ≤ 32 := by
  fin_cases label <;> decide +kernel

end ExplainableCrypto.Helios.Computational.BinaryModuloCode
