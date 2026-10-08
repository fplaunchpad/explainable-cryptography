import ExplainableCrypto.Helios.Computational.BitTapeInput
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink

/-! Replace both old answer halves after an oracle reply. The old after half has
already been replaced by the actual event with raw reply bits on port 1. -/
namespace ExplainableCrypto.Helios.Computational.NativeAnswerImport
open Turing OracleComp OracleSpec
open BitTapeCoverage (cellCode cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
abbrev Config := BitOracleMachine.Config 3 5 3
abbrev Statement := TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 5) (Fin 3)
def inputLayout : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
def inputLabel (q : Fin 3) : Fin 5 := ⟨q.val+2,by omega⟩
def inputProgram (q : Fin 3) := TM2StackFrame.relocate inputLayout (BitTapeInput.program q)
def clear (port : Fin 3) (again next : Fin 5) : Statement :=
  .pop port (fun _ b => cellCode b)
    (.branch (fun v => v ≠ 0) (.goto (fun _ => again)) (.goto (fun _ => next)))
def program : Fin 5 → Statement :=
  ![clear 0 0 1,clear 2 1 2,
    BitOracleReturnLink.stmt inputLabel none (inputProgram 0),
    BitOracleReturnLink.stmt inputLabel none (inputProgram 1),
    BitOracleReturnLink.stmt inputLabel none (inputProgram 2)]
def code : BitOracleMachine.Code 3 5 3 := fun q => .compute (program q)
def cfg (label : Option (Fin 5)) (v : Fin 3) (a b c : List Bool) : Config :=
  ⟨label,v,![a,b,c]⟩
def initial (oldBefore reply rawQuery : List Bool) : Config := cfg (some 0) 0 oldBefore reply rawQuery
def result (reply : List Bool) : Config :=
  cfg none (cellCode reply.head?) [] (cells (reply.tail.map some)) []
def clock (oldBefore reply rawQuery : List Bool) : Nat :=
  oldBefore.length+rawQuery.length+2*reply.length+5
def cost (oldBefore reply rawQuery : List Bool) : Nat := 5*clock oldBefore reply rawQuery

theorem input_code (q : Fin 3) :
    code (inputLabel q) = BitOracleReturnLink.command inputLabel none
      (BitOracleStackFrame.code inputLayout (fun q => .compute (BitTapeInput.program q)) q) := by
  fin_cases q <;> rfl

theorem local_cost (q : Fin 5) : BitOracleMachine.localCost (program q) ≤ 5 := by
  fin_cases q <;> decide +kernel

private theorem update_port (a b c word : List Bool) (k : Fin 3) :
    Function.update (![a,b,c] : Fin 3 → List Bool) k word =
      ![if k=0 then word else a,if k=1 then word else b,if k=2 then word else c] := by
  fin_cases k <;> funext j <;> fin_cases j <;> simp [Function.update]

theorem input_initial (reply : List Bool) :
    BitOracleReturnLink.embed inputLabel none
      (BitOracleStackFrame.embed inputLayout (BitTapeInput.initial reply) (fun _ => [])) =
      cfg (some 2) 0 [] reply [] := by
  apply congrArg (fun words : Fin 3 → List Bool => (⟨some 2,0,words⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem input_result (reply : List Bool) :
    BitOracleReturnLink.embed inputLabel none
      (BitOracleStackFrame.embed inputLayout
        (BitTapeCoverage.present (BitTapeInput.native (l := 3) none reply)) (fun _ => [])) =
      result reply := by
  apply congrArg (fun words : Fin 3 → List Bool =>
    (⟨none,cellCode reply.head?,words⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem clear_before_step (a b c : List Bool) (v : Fin 3) :
    TM2ReturnLink.tick program (cfg (some 0) v a b c) = match a with
    | [] => cfg (some 1) 0 [] b c
    | bit::rest => cfg (some 0) (cellCode (some bit)) rest b c := by
  cases a with
  | nil => simp [TM2ReturnLink.tick,TM2.step,TM2.stepAux,program,clear,cfg,cellCode,update_port]
  | cons bit rest => cases bit <;>
      simp [TM2ReturnLink.tick,TM2.step,TM2.stepAux,program,clear,cfg,cellCode,update_port]

private theorem clear_query_step (a b c : List Bool) (v : Fin 3) :
    TM2ReturnLink.tick program (cfg (some 1) v a b c) = match c with
    | [] => cfg (some 2) 0 a b []
    | bit::rest => cfg (some 1) (cellCode (some bit)) a b rest := by
  cases c with
  | nil => simp [TM2ReturnLink.tick,TM2.step,TM2.stepAux,program,clear,cfg,cellCode,update_port]
  | cons bit rest => cases bit <;>
      simp [TM2ReturnLink.tick,TM2.step,TM2.stepAux,program,clear,cfg,cellCode,update_port]

private theorem clear_before_run (a b c : List Bool) (v : Fin 3) :
    (TM2ReturnLink.tick program)^[a.length+1] (cfg (some 0) v a b c) =
      cfg (some 1) 0 [] b c := by
  induction a generalizing v with
  | nil => exact clear_before_step [] b c v
  | cons bit rest ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,clear_before_step,ih]

private theorem clear_query_run (a b c : List Bool) (v : Fin 3) :
    (TM2ReturnLink.tick program)^[c.length+1] (cfg (some 1) v a b c) =
      cfg (some 2) 0 a b [] := by
  induction c generalizing v with
  | nil => exact clear_query_step a b [] v
  | cons bit rest ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,clear_query_step,ih]

/-- Both old answer-left storage and the exported raw query are actually cleared
before the existing converter starts; the raw reply is unchanged. -/
theorem clear_run (oldBefore reply rawQuery : List Bool) :
    (TM2ReturnLink.tick program)^[oldBefore.length+rawQuery.length+2]
      (initial oldBefore reply rawQuery) = cfg (some 2) 0 [] reply [] := by
  rw [show oldBefore.length+rawQuery.length+2 =
    (rawQuery.length+1)+(oldBefore.length+1) by omega,Function.iterate_add_apply]
  rw [initial,clear_before_run,clear_query_run]

private theorem input_charged (reply : List Bool) :
    ∃ charge ≤ 5*(2*reply.length+3),
      BitOracleMachine.run code (2*reply.length+3) (cfg (some 2) 0 [] reply []) =
        pure (result reply,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost BitTapeInput.program 5
    BitTapeInput.local_cost (2*reply.length+3) (BitTapeInput.initial reply)
  rw [BitTapeInput.run] at he
  have hf := BitOracleStackFrame.run inputLayout (fun q => .compute (BitTapeInput.program q))
    (2*reply.length+3) (BitTapeInput.initial reply) (fun _ => [])
  rw [he,map_pure] at hf
  have hr := BitOracleReturnLink.rename_run
    (BitOracleStackFrame.code inputLayout (fun q => .compute (BitTapeInput.program q)))
    code inputLabel input_code (2*reply.length+3)
    (BitOracleStackFrame.embed inputLayout (BitTapeInput.initial reply) (fun _ => []))
  rw [hf,map_pure,input_initial,input_result] at hr
  exact ⟨charge,hc,hr⟩

/-- Instruction-derived charged replacement and encoding for every raw reply.
No restriction is imposed on the old encoded-left word or exported query. -/
theorem charged (oldBefore reply rawQuery : List Bool) :
    ∃ charge ≤ cost oldBefore reply rawQuery,
      BitOracleMachine.run code (clock oldBefore reply rawQuery)
        (initial oldBefore reply rawQuery) = pure (result reply,charge) := by
  obtain ⟨first,hfirst,he⟩ := BitOracleMachine.compute_run_cost program 5 local_cost
    (oldBefore.length+rawQuery.length+2) (initial oldBefore reply rawQuery)
  rw [clear_run] at he
  change BitOracleMachine.run code _ _ = _ at he
  obtain ⟨last,hlast,hl⟩ := input_charged reply
  refine ⟨first+last,?_,?_⟩
  · unfold cost clock
    omega
  · rw [show clock oldBefore reply rawQuery =
      (oldBefore.length+rawQuery.length+2)+(2*reply.length+3) by unfold clock; omega,
      BitOracleReturnLink.run_add,he,pure_bind,hl,pure_bind]

/-- Complete deterministic execution, including empty and false-leading replies,
with both old auxiliary words cleared and the new native head correctly loaded. -/
theorem run (oldBefore reply rawQuery : List Bool) :
    (TM2ReturnLink.tick program)^[clock oldBefore reply rawQuery]
      (initial oldBefore reply rawQuery) = result reply := by
  obtain ⟨charge,_,he⟩ := charged oldBefore reply rawQuery
  obtain ⟨actual,_,ha⟩ := BitOracleMachine.compute_run_cost program 5 local_cost
    (clock oldBefore reply rawQuery) (initial oldBefore reply rawQuery)
  change BitOracleMachine.run code _ _ = _ at ha
  rw [he] at ha
  exact (Prod.mk.inj ((OracleComp.pure_inj _ _).mp ha)).1.symm

end ExplainableCrypto.Helios.Computational.NativeAnswerImport
