import ExplainableCrypto.Helios.Computational.NativeQueryExport
import ExplainableCrypto.Helios.Computational.OracleTapeDispatch

/-! The exporter's contiguous prefix is the existing native query semantics,
for arbitrary finite representatives, including interior and trailing blanks. -/
namespace ExplainableCrypto.Helios.Computational.NativeQueryReadWord
open Turing

private theorem prefix_tape (before word : List (Option Bool)) :
    NativeQueryExport.wordPrefix word =
      OracleTapeDispatch.readWord (Tape.mk' (ListBlank.mk before) (ListBlank.mk word)) := by
  unfold OracleTapeDispatch.readWord
  rw [Tape.mk'_right₀]
  induction word with
  | nil => rfl
  | cons c word ih =>
    cases c with
    | none => rfl
    | some b => exact congrArg (List.cons b) ih

/-- Actual head and both arbitrary native halves; no dense/nonblank invariant. -/
theorem readWord {l : Nat} (label : Option (Fin l)) (head : Option Bool)
    (before after : List (Option Bool)) :
    NativeQueryExport.wordPrefix (head::after) =
      OracleTapeDispatch.readWord (BitTapeCoverage.tape ⟨label,head,before,after⟩) := by
  exact prefix_tape before (head::after)

end ExplainableCrypto.Helios.Computational.NativeQueryReadWord
