import ExplainableCrypto.Helios.Computational.BitOracleTapeOutput
import Mathlib.Data.Fin.VecNotation

/-! Physical query-tape controls with independently chosen nonpalindromic words
and a longer caller column. Mutants distinguish order and head restoration. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeOutputControls
open Turing TM2TapeRuns OracleTapeOutput

private def src : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
  ⟨some 0, true, ![[true, false, false], [false, true, true, false, true]]⟩

/-- The exact full-state theorem applies with no caller-supplied tape relation. -/
theorem derived_export :
    (step (0 : Fin 2))^[8] ⟨.copy, (pack src).Tape, wordTape []⟩ =
      ⟨.done, (pack src).Tape, wordTape [true, false, false]⟩ :=
  run_packed src 0

/-- Actual head-local steps emit the original word, stop at its first bit, and
restore the work head while retaining a longer neighboring column. -/
theorem actual_export :
    let out := (step (0 : Fin 2))^[8] ⟨.copy, (pack src).Tape, wordTape []⟩
    out.phase = .done ∧ out.query.head = some true ∧
    (out.query.move .right).head = some false ∧
    ((Tape.move .right)^[2] out.query).head = some false ∧
    ((Tape.move .right)^[3] out.query).head = none ∧
    out.work.head.1 = true ∧ out.work.head.2 1 = some true ∧
    ((Tape.move .right)^[4] out.work).head.2 1 = some false := by decide +kernel

private def wrongStep (c : OracleTapeOutput.Config (Fin 2)) : OracleTapeOutput.Config (Fin 2) :=
  match c.phase with
  | .copy => match c.work.head.2 0 with
    | some bit => ⟨.copy, c.work.move .right, (c.query.write (some bit)).move .right⟩
    | none => {c with phase := .back, query := c.query.move .left}
  | _ => step 0 c

/-- Rightward writing has the wrong ordinary word order. Inspect from its
leftmost written cell; moving its head cannot repair the reversed contents. -/
theorem rightward_write_fails :
    let out := wrongStep^[8] ⟨.copy, (pack src).Tape, wordTape []⟩
    ((Tape.move .left)^[2] out.query).head = some false ∧
    (wordTape [true, false, false]).head = some true := by decide +kernel

/-- Having emitted all query bits does not mean the caller work head is restored. -/
theorem return_is_required :
    let out := (step (0 : Fin 2))^[4] ⟨.copy, (pack src).Tape, wordTape []⟩
    out.phase = .back ∧ out.work.head.1 = false ∧ out.query.head = some true := by
  decide +kernel

/-- Empty requests still execute both boundary transitions and retain caller data. -/
theorem empty_export :
    let c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
      ⟨none, false, ![[], [true, false]]⟩
    (step (0 : Fin 2))^[2] ⟨.copy, (pack c).Tape, wordTape []⟩ =
      ⟨.done, (pack c).Tape, wordTape []⟩ := by
  exact run_packed (⟨none, false, ![[], [true, false]]⟩ :
    TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool) (0 : Fin 2)

/-- A stale native query suffix is observable: blank input is a real premise
until the complete oracle loop establishes cleanup between calls. -/
theorem stale_query_fails :
    let c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool := ⟨none, false, ![[], []]⟩
    let out := (step (0 : Fin 2))^[2] ⟨.copy, (pack c).Tape, wordTape [true, false]⟩
    out.query.head = some false ∧ out.phase = .done := by decide +kernel

/-- The added clearing phase removes the stale suffix before an empty request. -/
theorem stale_query_cleaned :
    let c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
      ⟨none, false, ![[], [true, false]]⟩
    (step (0 : Fin 2))^[5] ⟨.clear, (pack c).Tape, wordTape [true, false]⟩ =
      ⟨.done, (pack c).Tape, wordTape []⟩ := by
  exact run_replacing (⟨none, false, ![[], [true, false]]⟩ :
    TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool) (0 : Fin 2) [true, false]

end ExplainableCrypto.Helios.Computational.OracleTapeOutputControls
