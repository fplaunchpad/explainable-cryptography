import ExplainableCrypto.Helios.Computational.NativeWordCompiler

/-! Explicit failures of general native-program coverage for the fixed-probe
compiler. These are intended rejection controls, not compiler counterexamples
inside its stated dense-word supported-action boundary. -/
namespace ExplainableCrypto.Helios.Computational.NativeWordCompilerBoundary
open Turing OracleComp OracleSpec
open NativeWordCompiler
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

def blankWrite : NativeOracleTape.Code 2 := fun q _ =>
  if q = 0 then .local 1 ![some (.write none),none,none] else .halt

def rightBlank : NativeOracleTape.Code 2 := fun q _ =>
  if q = 0 then .local 1 ![some (.move .right),none,none] else .halt

def initialWords : Fin 6 → List Bool := ![[],[true],[],[],[],[]]
def emptyWords : Fin 6 → List Bool := fun _ => []

/-- A one-cell native erasure succeeds, but the mechanical dense compiler
explicitly halts with rejection memory 26 and retains the old cell. -/
theorem blank_write_native :
    NativeOracleTape.run blankWrite 2 (nativeConfig (some 0) initialWords) =
      pure (nativeConfig none emptyWords) := by rfl

theorem blank_write_target :
    BitOracleMachine.run (code blankWrite) 2 (start 0 initialWords) =
      pure (⟨none,26,initialWords⟩,6) := by rfl

/-- A move across the blank half is valid in the native tape semantics;
the finite dense representation deliberately rejects it. -/
theorem right_blank_native :
    NativeOracleTape.run rightBlank 2 (nativeConfig (some 0) emptyWords) =
      pure (⟨none,(tape [] []).move .right,tape [] [],tape [] []⟩ : NativeOracleTape.Config 2) := by rfl

theorem right_blank_target :
    BitOracleMachine.run (code rightBlank) 2 (start 0 emptyWords) =
      pure (⟨none,26,emptyWords⟩,9) := by
  have h : BitOracleMachine.run (code rightBlank) 2 (start 0 emptyWords) =
      pure (⟨none,26,Function.update emptyWords (1 : Fin 6) []⟩,9) := by rfl
  rw [h]
  rw [show Function.update emptyWords (1 : Fin 6) [] = emptyWords from
    Function.update_eq_self _ _]


/-- Rejection memory is observably different from successful target halt. -/
theorem rejection_not_success :
    (⟨none,26,initialWords⟩ : Config 2) ≠ present none initialWords := by
  intro h
  have hm := congrArg (fun c : Config 2 => c.var) h
  have hn := congrArg Fin.val hm
  norm_num [present] at hn

end ExplainableCrypto.Helios.Computational.NativeWordCompilerBoundary
