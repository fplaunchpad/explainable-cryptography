import ExplainableCrypto.Helios.Computational.BitPairWriterMachineRun

namespace ExplainableCrypto.Helios.Computational.BitPairWriterMachineControls
open BitPairWriterMachine Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
private def view (cfg : BitPairWriterMachine.Config) := (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)

/-- Independent literal complete7-port pair result: empty both. -/
theorem empty_both :
    view (tick^[clock 0 0] (start [] [])) =
      (none,2,List.ofFn (![[],[],[true,true,false,false,true,false,false],[],[],[],[]] : Fin 7 → List Bool)) := by
  rw [show clock 0 0 = clock [].length [].length from rfl,padded_run]
  decide +kernel
#print axioms empty_both

/-- Independent literal complete7-port pair result: empty left. -/
theorem empty_left :
    view (tick^[clock 0 5] (start [] [true,false,true,true,false])) =
      (none,2,List.ofFn (![[],[true,false,true,true,false],[true,true,false,false,true,false,true,true,true,false,true,false,true,true,false,true,true,false],[],[],[],[]] : Fin 7 → List Bool)) := by
  rw [show clock 0 5 = clock [].length [true,false,true,true,false].length from rfl,padded_run]
  decide +kernel
#print axioms empty_left

/-- Independent literal complete7-port pair result: empty right. -/
theorem empty_right :
    view (tick^[clock 3 0] (start [false,true,true] [])) =
      (none,2,List.ofFn (![[false,true,true],[],[true,true,false,false,true,true,true,false,true,true,false,true,true,false],[],[],[],[]] : Fin 7 → List Bool)) := by
  rw [show clock 3 0 = clock [false,true,true].length [].length from rfl,padded_run]
  decide +kernel
#print axioms empty_right

/-- Independent literal complete7-port pair result: nonpalindromic. -/
theorem nonpalindromic :
    view (tick^[clock 5 3] (start [true,false,true,true,false] [false,true,true])) =
      (none,2,List.ofFn (![[true,false,true,true,false],[false,true,true],[true,true,false,false,true,true,true,true,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true],[],[],[],[]] : Fin 7 → List Bool)) := by
  rw [show clock 5 3 = clock [true,false,true,true,false].length [false,true,true].length from rfl,padded_run]
  decide +kernel
#print axioms nonpalindromic

/-- Independent literal complete7-port pair result: singletons. -/
theorem singletons :
    view (tick^[clock 1 1] (start [false] [true])) =
      (none,2,List.ofFn (![[false],[true],[true,true,false,false,true,true,false,true,false,true,false,true,true],[],[],[],[]] : Fin 7 → List Bool)) := by
  rw [show clock 1 1 = clock [false].length [true].length from rfl,padded_run]
  decide +kernel
#print axioms singletons

/-- Independent literal complete7-port pair result: width boundary. -/
theorem width_boundary :
    view (tick^[clock 16 17] (start [false,true,true,false,true,false,false,true,true,true,false,true,false,false,true,true] [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true])) =
      (none,2,List.ofFn (![[false,true,true,false,true,false,false,true,true,true,false,true,false,false,true,true],[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true],[true,true,false,false,true,true,true,true,true,true,false,false,false,false,false,true,false,true,true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,true,true,true,false,true,false,false,false,true,true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true],[],[],[],[]] : Fin 7 → List Bool)) := by
  rw [show clock 16 17 = clock [false,true,true,false,true,false,false,true,true,true,false,true,false,false,true,true].length [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true].length from rfl,padded_run]
  decide +kernel
#print axioms width_boundary

/-- Unequal nonpalindromes rule out swapping the two fields. -/
theorem field_order_matters :
    (tick^[clock 5 3] (start [true,false,true,true,false] [false,true,true])).stk 2 ≠ [true,true,false,false,true,true,true,false,true,true,false,true,true,true,true,true,false,true,false,true,true,false,true,true,false] := by
  rw [show clock 5 3 = clock [true,false,true,true,false].length [false,true,true].length from rfl,padded_run]
  decide +kernel
private def withoutCount (l : Fin size) :=
  if l=2 then Stmt.load (fun _ : Fin 3 => 2) .halt else program l
private def finalInput : BitPairWriterMachine.Config :=
  ⟨some 2,2,![[true,false,true,true,false],[false,true,true],[true,true,true,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true],[],[],[],[]]⟩
/-- The actual finish instruction emits the pair count prefix. -/
theorem original_count_prefix : tick finalInput = result [true,false,true,true,false] [false,true,true] := by
  change (⟨_,_,_⟩ : BitPairWriterMachine.Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> decide +kernel
/-- Omitting that actual instruction gives a distinct complete result. -/
theorem missing_count_is_detected :
    view ((TM2ReturnLink.tick withoutCount) finalInput) ≠ view (result [true,false,true,true,false] [false,true,true]) := by decide +kernel
/-- The entry success guard rejects a failed preceding component without modifying words. -/
theorem failed_entry_rejects :
    view (tick (⟨some 0,1,![[true,false,true,true,false],[false,true,true],[],[],[],[],[]]⟩ : BitPairWriterMachine.Config)) =
      (none,1,List.ofFn (![ [true,false,true,true,false],[false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
#print axioms field_order_matters
#print axioms original_count_prefix
#print axioms missing_count_is_detected
#print axioms failed_entry_rejects
end ExplainableCrypto.Helios.Computational.BitPairWriterMachineControls
