import ExplainableCrypto.Helios.Computational.BitOracleTapeInput
import Mathlib.Data.Fin.VecNotation

/-! Literal incoming replacement controls, with independent expected words and
mutated erasure, direction and column selection. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeInputControls
open Turing TM2TapeRuns OracleTapeOutput OracleTapeInput

private def src : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
  ⟨some 0, true, ![[true, true, true, true], [false, true, false, false, true]]⟩
private def initial : OracleTapeInput.Config (Fin 2) :=
  ⟨.seekWork, (pack src).Tape, wordTape [true, false, false]⟩

/-- The general theorem derives an exact shorter replacement and full frame. -/
theorem derived_load :
    (OracleTapeInput.step (0 : Fin 2))^[30] initial =
      ⟨.done, (pack {src with stk := ![[true, false, false], [false, true, false, false, true]]}).Tape,
        wordTape [true, false, false]⟩ := by
  have h := OracleTapeInput.run_packed src (0 : Fin 2) [true, false, false]
  have he : Function.update src.stk (0 : Fin 2) [true, false, false] =
      ![[true, false, false], [false, true, false, false, true]] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at h
  have hn : 3 * (src.stk 0).length + 4 * [true, false, false].length + 6 = 30 := by decide +kernel
  rw [hn] at h
  exact h

/-- Literal execution retains the nonpalindrome, erases the old fourth bit,
restores both heads and preserves a longer other column. -/
theorem actual_load :
    let out := (OracleTapeInput.step (0 : Fin 2))^[30] initial
    out.phase = .done ∧ out.work.head.1 = true ∧ out.work.head.2 0 = some false ∧
    ((Tape.move .right)^[2] out.work).head.2 0 = some true ∧
    ((Tape.move .right)^[3] out.work).head.2 0 = none ∧
    ((Tape.move .right)^[4] out.work).head.2 1 = some false ∧
    out.answer.head = some true ∧ (out.answer.move .right).head = some false ∧
    ((Tape.move .right)^[2] out.answer).head = some false ∧
    ((Tape.move .right)^[3] out.answer).head = none := by decide +kernel

private def noErase (c : OracleTapeInput.Config (Fin 2)) : OracleTapeInput.Config (Fin 2) :=
  if c.phase = .eraseCell then {c with phase := .erase} else OracleTapeInput.step 0 c
private def wrongDirection (c : OracleTapeInput.Config (Fin 2)) : OracleTapeInput.Config (Fin 2) :=
  if c.phase = .loadLeft then ⟨.write, c.work, c.answer.move .right⟩ else OracleTapeInput.step 0 c
private def wrongColumn (c : OracleTapeInput.Config (Fin 2)) : OracleTapeInput.Config (Fin 2) :=
  if c.phase = .write then OracleTapeInput.step 1 c else OracleTapeInput.step 0 c

/-- Omitting erasure leaves a stale fourth bit after a shorter answer. -/
theorem old_suffix_fails :
    ((Tape.move .right)^[3] (noErase^[30] initial).work).head.2 0 = some true := by decide +kernel

/-- Moving away from the native word loads no bits, even though a reply exists. -/
theorem wrong_direction_fails :
    (wrongDirection^[30] initial).work.head.2 0 = none := by decide +kernel

/-- Selecting a caller column instead of the private column corrupts its bottom bit. -/
theorem other_column_fails :
    (wrongColumn^[30] initial).work.head.2 1 = some false ∧
    (pack src).Tape.head.2 1 = some true := by decide +kernel

/-- An empty answer erases all old private bits and leaves the other column intact. -/
theorem empty_answer :
    let out := (OracleTapeInput.step (0 : Fin 2))^[18]
      ⟨.seekWork, (pack src).Tape, wordTape []⟩
    out.phase = .done ∧ out.work.head.2 0 = none ∧ out.work.head.2 1 = some true ∧
    ((Tape.move .right)^[3] out.work).head.2 0 = none ∧ out.answer.head = none := by decide +kernel

end ExplainableCrypto.Helios.Computational.OracleTapeInputControls
