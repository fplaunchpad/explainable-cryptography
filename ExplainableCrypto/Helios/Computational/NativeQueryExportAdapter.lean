import ExplainableCrypto.Helios.Computational.NativeQueryExport
import ExplainableCrypto.Helios.Computational.NativeQueryReadWord
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink

/-! Actual head-register preparation and restoration around general cell export.
This adapter starts with the existing head register and encoded after cells.
The two head bits are pushed and removed by executed instructions. -/
namespace ExplainableCrypto.Helios.Computational.NativeQueryExportAdapter
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cellCode readCell cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

abbrev Config := BitOracleMachine.Config 3 4 3
abbrev Statement := TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (Fin 3)

def coreLabel (q : Fin 2) : Fin 4 := ⟨q.val+1,by have := q.isLt; omega⟩

def entry : Statement :=
  .push 0 (fun v => (readCell v).getD false)
    (.push 0 (fun v => (readCell v).isSome) (.goto (fun _ => 1)))

def exitStmt : Statement :=
  .pop 0 (fun _ tag => if tag.getD false then 1 else 0)
    (.pop 0 (fun v bit => if v = 0 then 0 else cellCode (some (bit.getD false))) .halt)

def program : Fin 4 → Statement :=
  ![entry,TM2ReturnLink.redirect coreLabel 3 (NativeQueryExport.program 0),
    TM2ReturnLink.redirect coreLabel 3 (NativeQueryExport.program 1),exitStmt]

def code : BitOracleMachine.Code 3 4 3 := fun q => .compute (program q)

def initial (head : Cell) (after : List Cell) : Config :=
  ⟨some 0,cellCode head,![cells after,[],[]]⟩

def result (head : Cell) (after : List Cell) : Config :=
  ⟨none,cellCode head,![cells after,NativeQueryExport.wordPrefix (head::after),[]]⟩

def clock (head : Cell) (after : List Cell) := NativeQueryExport.clock (head::after)+2
def cost (head : Cell) (after : List Cell) := 6*clock head after

theorem program_core (q : Fin 2) :
    program (coreLabel q) = TM2ReturnLink.redirect coreLabel 3 (NativeQueryExport.program q) := by
  fin_cases q <;> rfl

private theorem update_source (a b c value : List Bool) :
    Function.update (![a,b,c] : Fin 3 → List Bool) (0 : Fin 3) value = ![value,b,c] := by
  funext k
  fin_cases k <;> simp [Function.update]

/-- The current head is actually written in front of the original after cells. -/
theorem entry_step (head : Cell) (after : List Cell) :
    TM2ReturnLink.tick program (initial head after) =
      TM2ReturnLink.embed coreLabel 3 (NativeQueryExport.start (head::after) [] (cellCode head)) := by
  fin_cases head <;>
    simp [TM2ReturnLink.tick,TM2.step,TM2.stepAux,program,entry,initial,
      TM2ReturnLink.embed,NativeQueryExport.start,NativeQueryExport.state,
      coreLabel,cells,cellCode,readCell,update_source]

/-- Only the prepended head is removed; its actual tag/payload restore the register. -/
theorem exit_step (head : Cell) (after : List Cell) :
    TM2ReturnLink.tick program
      (TM2ReturnLink.embed coreLabel 3 (NativeQueryExport.result (head::after))) =
      result head after := by
  fin_cases head <;>
    simp [TM2ReturnLink.tick,TM2.step,TM2.stepAux,program,exitStmt,result,
      TM2ReturnLink.embed,NativeQueryExport.result,NativeQueryExport.state,
      cells,cellCode,update_source]

theorem local_cost (q : Fin 4) : BitOracleMachine.localCost (program q) ≤ 6 := by
  fin_cases q <;> decide +kernel

/-- Execute preparation, the existing preserving exporter and head restoration.
Return linking removes any internal halted padding; padding is added only after
this complete adapter has reached its restored final halt. -/
theorem run (head : Cell) (after : List Cell) :
    (TM2ReturnLink.tick program)^[clock head after] (initial head after) = result head after := by
  have hc := NativeQueryExport.run (head::after) [] (cellCode head)
  have hh : ((TM2ReturnLink.tick NativeQueryExport.program)^[NativeQueryExport.clock (head::after)]
      (NativeQueryExport.start (head::after) [] (cellCode head))).l = none := by
    rw [hc]
    rfl
  obtain ⟨used,hu,he⟩ := TM2ReturnLink.run NativeQueryExport.program program coreLabel 3
    program_core (NativeQueryExport.clock (head::after))
    (NativeQueryExport.start (head::after) [] (cellCode head)) hh
  rw [hc] at he
  have done : (TM2ReturnLink.tick program)^[used+2] (initial head after) = result head after := by
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply,entry_step,he]
    exact exit_step head after
  have hle : used+2 ≤ clock head after := by unfold clock; omega
  rw [show clock head after = (clock head after-(used+2))+(used+2) by omega,
    Function.iterate_add_apply,done]
  exact Function.iterate_fixed
    (show TM2ReturnLink.tick program (result head after) = result head after from rfl) _

/-- The executed finite program itself provides the complete export cost. -/
theorem charged (head : Cell) (after : List Cell) :
    ∃ charge ≤ cost head after,
      BitOracleMachine.run code (clock head after) (initial head after) =
        pure (result head after,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 6 local_cost
    (clock head after) (initial head after)
  rw [run] at he
  exact ⟨charge,hc,he⟩

end ExplainableCrypto.Helios.Computational.NativeQueryExportAdapter
