import ExplainableCrypto.Helios.Computational.BitOracleMachine
import ExplainableCrypto.Helios.Computational.TM2StackFrame

/-! Lift existing oracle code to a larger workspace. Deterministic instructions
use `TM2StackFrame`; oracle requests and replacement replies retain the frame.
The complete query tree and exact accumulated charge are preserved. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleStackFrame
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
variable {s e t l m : Nat}

def command (layout : Fin s ⊕ Fin e ≃ Fin t) : Command s l m → Command t l m
  | .compute q => .compute (TM2StackFrame.relocate layout q)
  | .coin dest next => .coin (layout (.inl dest)) next
  | .hash req dest next => .hash (layout (.inl req)) (layout (.inl dest)) next

def code (layout : Fin s ⊕ Fin e ≃ Fin t) (p : Code s l m) : Code t l m :=
  fun label => command layout (p label)

abbrev embed (layout : Fin s ⊕ Fin e ≃ Fin t) (cfg : Config s l m)
    (frame : Fin e → List Bool) : Config t l m := TM2StackFrame.embed layout cfg frame

private theorem data_update (layout : Fin s ⊕ Fin e ≃ Fin t)
    (words : Fin s → List Bool) (frame : Fin e → List Bool) (dest : Fin s) (answer : List Bool) :
    TM2StackFrame.data layout (Function.update words dest answer) frame =
      Function.update (TM2StackFrame.data layout words frame) (layout (.inl dest)) answer := by
  funext j
  obtain ⟨x,rfl⟩ := layout.surjective j
  cases x <;> simp [TM2StackFrame.data,Function.update,layout.injective.eq_iff]

theorem local_cost (layout : Fin s ⊕ Fin e ≃ Fin t)
    (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    localCost (TM2StackFrame.relocate layout q) = localCost q := by
  induction q <;> simp_all [TM2StackFrame.relocate,localCost]

/-- One actual command keeps every extra port, including across oracle replies. -/
theorem step (layout : Fin s ⊕ Fin e ≃ Fin t) (p : Code s l m)
    (cfg : Config s l m) (frame : Fin e → List Bool) :
    BitOracleMachine.step (code layout p) (embed layout cfg frame) =
      (fun out => (embed layout out.1 frame,out.2)) <$> BitOracleMachine.step p cfg := by
  rcases cfg with ⟨label,v,words⟩
  cases label with
  | none => simp [BitOracleMachine.step,embed,TM2StackFrame.embed]
  | some label =>
    cases h : p label with
    | compute q =>
      simp [BitOracleMachine.step,code,command,h,embed,TM2StackFrame.embed,
        TM2StackFrame.statement,local_cost]
    | coin dest next =>
      simp [BitOracleMachine.step,code,command,h,embed,TM2StackFrame.embed,
        resume,← data_update,TM2StackFrame.data]
    | hash req dest next =>
      simp only [BitOracleMachine.step,code,command,h,embed,TM2StackFrame.embed,
        TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl,map_bind,map_pure]
      congr 1
      · congr 2
        simp
      · funext answer
        simp only [resume]
        rw [data_update layout words frame dest answer]

/-- All finite observations preserve the full oracle tree and exact charge.
No termination, response-size or correspondence certificate is assumed. -/
theorem run (layout : Fin s ⊕ Fin e ≃ Fin t) (p : Code s l m)
    (fuel : Nat) (cfg : Config s l m) (frame : Fin e → List Bool) :
    BitOracleMachine.run (code layout p) fuel (embed layout cfg frame) =
      (fun out => (embed layout out.1 frame,out.2)) <$> BitOracleMachine.run p fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp [BitOracleMachine.run]
  | succ fuel ih =>
    rw [BitOracleMachine.run,step]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    simp only [BitOracleMachine.run,bind_assoc,pure_bind]
    apply bind_congr
    intro first
    rw [ih]
    simp [map_eq_bind_pure_comp,bind_assoc]

end ExplainableCrypto.Helios.Computational.BitOracleStackFrame
