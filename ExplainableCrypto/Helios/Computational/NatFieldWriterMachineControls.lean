import ExplainableCrypto.Helios.Computational.NatFieldWriterMachineRun
namespace ExplainableCrypto.Helios.Computational.NatFieldWriterMachineControls
open NatFieldWriterMachine Turing.TM2 BitOracleMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 800000
private def view (cfg : NatFieldWriterMachine.Config) := (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)
private def changed (m : Nat) (l : Fin 21) :=
  if m == 1 && l == 0 then Stmt.load (fun _ => 0) (.goto (fun _ => prefixLabel 5))
  else if m == 2 && l == 2 then .load (fun _ => 2) .halt
  else if m == 3 && l == 2 then .push 1 (fun _ => false) (program l)
  else if m == 4 && l == 2 then .push 0 (fun _ => false) (program l)
  else if m == 5 && l == 0 then .load (fun _ => 0) (.goto (fun _ => copyLabel 0))
  else program l
theorem zero_empty : view (tick^[23] (start [] [])) = (none,2,List.ofFn (![[],[true,false,true,false],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem zero_suffix : view (tick^[23] (start [] [true,false,true,true])) = (none,2,List.ofFn (![[],[true,false,true,false,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem width_boundary : view (tick^[162] (start [false,false,false,true] [true,false,true,true])) = (none,2,List.ofFn (![[false,false,false,true],[true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,false,true,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem larger_width_boundary : view (tick^[358] (start [false,false,false,false,false,false,false,false,true] [true,false,true,true])) = (none,2,List.ofFn (![[false,false,false,false,false,false,false,false,true],[true,true,true,true,true,false,true,true,false,false,true,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,false,false,false,true,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem skip_copy_detected : view ((TM2ReturnLink.tick (changed 1))^[87] (start [false,true] [true,false,true,true])) ≠ (none,2,List.ofFn (![[false,true],[true,true,true,false,true,false,true,true,true,false,false,true,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem skip_field_detected : view ((TM2ReturnLink.tick (changed 2))^[87] (start [false,true] [true,false,true,true])) ≠ (none,2,List.ofFn (![[false,true],[true,true,true,false,true,false,true,true,true,false,false,true,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem suffix_corruption_detected : view ((TM2ReturnLink.tick (changed 3))^[87] (start [false,true] [true,false,true,true])) ≠ (none,2,List.ofFn (![[false,true],[true,true,true,false,true,false,true,true,true,false,false,true,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem source_corruption_detected : view ((TM2ReturnLink.tick (changed 4))^[87] (start [false,true] [true,false,true,true])) ≠ (none,2,List.ofFn (![[false,true],[true,true,true,false,true,false,true,true,true,false,false,true,true,false,true,true],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem failed_entry_rejected : view (tick^[1] (⟨some 0,1,![[false,true],[true,false],[],[],[],[],[]]⟩ : NatFieldWriterMachine.Config)) =
  (none,1,List.ofFn (![[false,true],[true,false],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
theorem failed_entry_bypass_detected : view ((TM2ReturnLink.tick (changed 5))^[87] (⟨some 0,1,![[false,true],[true,false],[],[],[],[],[]]⟩ : NatFieldWriterMachine.Config)) = (none,2,List.ofFn (![[false,true],[true,true,true,false,true,false,true,true,true,false,false,true,true,false],[],[],[],[],[]] : Fin 7 → List Bool)) := by decide +kernel
#print axioms zero_empty
#print axioms zero_suffix
#print axioms width_boundary
#print axioms larger_width_boundary
#print axioms skip_copy_detected
#print axioms skip_field_detected
#print axioms suffix_corruption_detected
#print axioms source_corruption_detected
#print axioms failed_entry_rejected
#print axioms failed_entry_bypass_detected
end ExplainableCrypto.Helios.Computational.NatFieldWriterMachineControls
