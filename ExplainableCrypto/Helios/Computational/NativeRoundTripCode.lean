import ExplainableCrypto.Helios.Computational.NativeRoundTrip

namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

theorem code_entry {l : Nat} (p : NativeOracleTape.Code l) (q : Fin l) :
    code p (entryLabel q) = .compute (entry p q) := by
  simp [code,entryLabel]

theorem code_block {l : Nat} (p : NativeOracleTape.Code l)
    (next : Fin l) (kind : Fin 2) (phase : Fin 13) :
    code p (blockLabel next kind phase) = block next kind phase := by
  simp [code,blockLabel]

theorem atNative_entry {l : Nat} (q : Fin l) : atNative (entryLabel q) = true := by
  simp [atNative,entryLabel]

theorem atNative_block {l : Nat} (next : Fin l) (kind : Fin 2) (phase : Fin 13) :
    atNative (blockLabel next kind phase) = false := by
  simp [atNative,blockLabel]

theorem code_export {l : Nat} (p : NativeOracleTape.Code l)
    (next : Fin l) (kind : Fin 2) (phase : Fin 4) :
    code p (exportLabel next kind phase) = .compute
      (TM2ReturnLink.redirect (exportLabel next kind) (blockLabel next kind 5) (exportProgram phase)) := by
  unfold exportLabel
  rw [code_block]
  fin_cases phase <;> rfl

theorem code_import {l : Nat} (p : NativeOracleTape.Code l)
    (next : Fin l) (kind : Fin 2) (phase : Fin 5) :
    code p (importLabel next kind phase) = .compute
      (TM2ReturnLink.redirect (importLabel next kind) (blockLabel next kind 12) (importProgram phase)) := by
  unfold importLabel
  rw [code_block]
  fin_cases phase <;> rfl

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
