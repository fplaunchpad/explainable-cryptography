import ExplainableCrypto.Helios.Computational.BitTapeCoverage
import ExplainableCrypto.Helios.Computational.BitOracleInitialInput

/-! Execute raw-word conversion into the existing three-symbol native tape
representation using the same two work stacks and finite cell register. -/
namespace ExplainableCrypto.Helios.Computational.BitTapeInput
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cellCode readCell cells)

/-- Reverse, encode, then extract the current cell. -/
def program : Fin 3 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 3) (Fin 3) := fun q =>
  if q = 0 then
    .pop 1 (fun _ bit => cellCode bit) <|
      .branch (fun v => v ≠ 0)
        (.push 0 (fun v => (readCell v).getD false) (.goto (fun _ => 0)))
        (.goto (fun _ => 1))
  else if q = 1 then
    .pop 0 (fun _ bit => cellCode bit) <|
      .branch (fun v => v ≠ 0)
        (.push 1 (fun v => (readCell v).getD false)
          (.push 1 (fun _ => true) (.goto (fun _ => 1))))
        (.goto (fun _ => 2))
  else
    .pop 1 (fun _ tag => if tag.getD false then 1 else 0)
      (.pop 1 (fun v bit => if v = 0 then 0 else cellCode (some (bit.getD false))) .halt)

private def cfg (label : Option (Fin 3)) (memory : Fin 3) (a b : List Bool) :
    BitOracleMachine.Config 2 3 3 := ⟨label, memory, ![a,b]⟩

def initial (word : List Bool) : BitOracleMachine.Config 2 3 3 :=
  cfg (some 0) 0 [] word

/-- The ordinary input tape: head on the first bit, no cells to its left. -/
def native {l : Nat} (label : Option (Fin l)) (word : List Bool) : BitTapeCoverage.Config l :=
  ⟨label, word.head?, [], word.tail.map some⟩

private theorem update_zero (a b word : List Bool) :
    Function.update ![a,b] (0 : Fin 2) word = ![word,b] := by
  funext k; fin_cases k <;> simp [Function.update]

private theorem update_one (a b word : List Bool) :
    Function.update ![a,b] (1 : Fin 2) word = ![a,word] := by
  funext k; fin_cases k <;> simp [Function.update]

private theorem reverse_step (a b : List Bool) (v : Fin 3) :
    TM2ReturnLink.tick program (cfg (some 0) v a b) = match b with
      | [] => cfg (some 1) 0 a []
      | bit :: rest => cfg (some 0) (cellCode (some bit)) (bit :: a) rest := by
  cases b with
  | nil => simp [TM2ReturnLink.tick, TM2.step, TM2.stepAux, program, cfg, cellCode, update_one]
  | cons bit rest => cases bit <;>
      simp [TM2ReturnLink.tick, TM2.step, TM2.stepAux, program, cfg, cellCode, readCell,
        update_one, update_zero]

private theorem encode_step (a b : List Bool) (v : Fin 3) :
    TM2ReturnLink.tick program (cfg (some 1) v a b) = match a with
      | [] => cfg (some 2) 0 [] b
      | bit :: rest => cfg (some 1) (cellCode (some bit)) rest (true :: bit :: b) := by
  cases a with
  | nil => simp [TM2ReturnLink.tick, TM2.step, TM2.stepAux, program, cfg, cellCode, update_zero]
  | cons bit rest => cases bit <;>
      simp [TM2ReturnLink.tick, TM2.step, TM2.stepAux, program, cfg, cellCode, readCell,
        update_zero, update_one]

private theorem reverse_run (a b : List Bool) (v : Fin 3) :
    (TM2ReturnLink.tick program)^[b.length + 1] (cfg (some 0) v a b) =
      cfg (some 1) 0 (b.reverse ++ a) [] := by
  induction b generalizing a v with
  | nil => exact reverse_step a [] v
  | cons bit rest ih =>
    rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, reverse_step, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem cells_append (a b : List Cell) : cells (a ++ b) = cells a ++ cells b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => simp [cells, ih]

private theorem encode_run (a b : List Bool) (v : Fin 3) :
    (TM2ReturnLink.tick program)^[a.length + 1] (cfg (some 1) v a b) =
      cfg (some 2) 0 [] (cells (a.reverse.map some) ++ b) := by
  induction a generalizing b v with
  | nil => exact encode_step [] b v
  | cons bit rest ih =>
    rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, encode_step, ih]
    simp [List.reverse_cons, List.map_append, cells_append, cells, List.append_assoc]

private theorem head_step (word : List Bool) :
    TM2ReturnLink.tick program (cfg (some 2) 0 [] (cells (word.map some))) =
      BitTapeCoverage.present (native (l := 3) none word) := by
  cases word with
  | nil => simp [TM2ReturnLink.tick, TM2.step, TM2.stepAux, program, cfg, native,
      BitTapeCoverage.present, cells, cellCode, update_one]
  | cons bit rest => cases bit <;>
      simp [TM2ReturnLink.tick, TM2.step, TM2.stepAux, program, cfg, native,
        BitTapeCoverage.present, cells, cellCode, update_one]

/-- Exact executed conversion of every raw word, including empty input and
false bits. Scratch is empty and the head/remaining cells have native order. -/
theorem run (word : List Bool) :
    (TM2ReturnLink.tick program)^[2 * word.length + 3] (initial word) =
      BitTapeCoverage.present (native (l := 3) none word) := by
  have hn : 2 * word.length + 3 = 1 + ((word.length + 1) + (word.length + 1)) := by omega
  rw [hn, Function.iterate_add_apply, Function.iterate_add_apply]
  rw [initial, reverse_run]
  simp only [List.append_nil]
  have he := encode_run word.reverse [] 0
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at he
  rw [he]
  exact head_step word

/-- Conversion's source statements have fixed finite cost. -/
theorem local_cost (q : Fin 3) : BitOracleMachine.localCost (program q) ≤ 5 := by
  fin_cases q <;> decide +kernel

end ExplainableCrypto.Helios.Computational.BitTapeInput
