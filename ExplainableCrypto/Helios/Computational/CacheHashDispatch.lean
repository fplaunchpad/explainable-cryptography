import ExplainableCrypto.Helios.Computational.CacheRoutineCode
import ExplainableCrypto.Helios.Computational.CacheHashMachine

/-! One finite-control cache request. The code connects the original probe,
executed miss sampler, hit writer, insertion and chronological append. General
source correspondence and the combined bound are proved separately. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashDispatch
open Turing.TM2 BitOracleMachine CacheRoutineCode

private def copyPorts : BitCopyMachine.Stack ≃ Fin 3 where
  toFun | .source => 0 | .destination => 1 | .scratch => 2
  invFun k := if k = 0 then .source else if k = 1 then .destination else .scratch
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

private def copyLabels : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun k := k == 1
  left_inv b := by cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl

/-- Answer 5 -> 7; original cache 9 -> 0; newly appended log 6 -> 10. -/
private def copyTable (which : Fin 3) : List (Fin 12) :=
  ![[5,7,0,1,2,3,4,6,8,9,10,11],
    [9,0,2,1,3,4,5,6,7,8,10,11],
    [6,10,0,1,2,3,4,5,7,8,9,11]] which

def copyLayout (which : Fin 3) : BitCopyMachine.Stack ⊕ Fin 9 ≃ Fin 12 :=
  ((Equiv.sumCongr copyPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 12 = (copyTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (copyTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))

def copyCode (which : Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) copyLabels BinaryModuloCode.memory
    (fun label => TM2StackFrame.relocate (copyLayout which) (BitCopyMachine.program label))

def copyState (which : Fin 3) (cfg : BitCopyMachine.Config) (frame : Fin 9 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl _) copyLabels BinaryModuloCode.memory
    (TM2StackFrame.embed (copyLayout which) cfg frame)

private theorem copy_cost : ∀ which label, localCost (copyCode which label) ≤ 5 := by
  decide +kernel

/-- Each actual dispatcher copy restores its source, prepends to the destination,
clears scratch, preserves the entire extra frame and derives its charge. -/
theorem copy_run (which : Fin 3) (source suffix : List Bool) (frame : Fin 9 → List Bool) :
    ∃ charge ≤ 5*(2*source.length+2),
      run (fun label => .compute (copyCode which label)) (2*source.length+2)
        (copyState which (BitCopyMachine.config (some false) source suffix []) frame) =
      pure (copyState which (BitCopyMachine.config none source (source++suffix) []) frame,charge) := by
  obtain ⟨charge,hc,he⟩ := compute_run_cost (copyCode which) 5 (copy_cost which) (2*source.length+2)
    (copyState which (BitCopyMachine.config (some false) source suffix []) frame)
  refine ⟨charge,hc,?_⟩
  rw [he]
  congr 2
  rw [copyState,copyCode,TM2FiniteCoordinates.run,TM2StackFrame.run]
  rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*source.length+2]
    (BitCopyMachine.config (some false) source suffix []) =
    BitCopyMachine.config none source (source++suffix) [] from BitCopyMachine.run source suffix none]
  rfl

def size : Nat := 12+readSize+47+writerSize+insertSize+appendSize+6
instance : NeZero size := ⟨by unfold size; omega⟩

def readLabel (label : Fin readSize) : Fin size := ⟨12+label.val,by unfold size; omega⟩
def sampleLabel (label : Fin 47) : Fin size := ⟨12+readSize+label.val,by unfold size; omega⟩
def writerLabel (label : Fin writerSize) : Fin size := ⟨12+readSize+47+label.val,by unfold size; omega⟩
def insertLabel (label : Fin insertSize) : Fin size := ⟨12+readSize+47+writerSize+label.val,by unfold size; omega⟩
def appendLabel (label : Fin appendSize) : Fin size := ⟨12+readSize+47+writerSize+insertSize+label.val,by unfold size; omega⟩
def copyLabel (which : Fin 3) (label : Fin 2) : Fin size :=
  ⟨12+readSize+47+writerSize+insertSize+appendSize+2*which.val+label.val,by unfold size; omega⟩

def fail : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) := .load (fun _ => 0) .halt

def enter (next : Fin size) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))

def success : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) := .load (fun _ => 2) .halt

def clear (port : Fin 12) (again : Fin size)
    (next : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3)) :
    Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  .pop port (fun _ b => CoinWordLoader.encode b)
    (.branch (fun v => v == 0) next (.goto (fun _ => again)))

def control (label : Fin 12) : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3) :=
  ![enter (readLabel (readLabels default)),
    .branch (fun v => v == 2) (enter 2) (.branch (fun v => v == 1) (enter 4) fail),
    clear 0 2 (enter (writerLabel (writerLabels .digits))),
    clear 4 3 success,
    enter (sampleLabel 0),
    .branch (fun v => v == 2) (enter (copyLabel 0 0)) fail,
    clear 5 6 (enter 7),
    clear 1 7 (enter (copyLabel 1 0)),
    clear 9 8 (enter (insertLabel (insertLabels default))),
    .branch (fun v => v == 2) (enter (appendLabel (appendLabels default))) fail,
    .branch (fun v => v == 2) (enter (copyLabel 2 0)) fail,
    clear 6 11 success] label

/-- Fixed dispatch code. Each subroutine halt jumps to its actual next phase. -/
def code (label : Fin size) : Command 12 size 3 :=
  if h : label.val < 12 then .compute (control ⟨label.val,h⟩)
  else if h : label.val < 12+readSize then
    BitOracleReturnLink.command readLabel (some 1) (.compute (readCode ⟨label.val-12,by omega⟩))
  else if h : label.val < 12+readSize+47 then
    BitOracleReturnLink.command sampleLabel (some 5) (CacheHashMachine.sampleCode ⟨label.val-(12+readSize),by omega⟩)
  else if h : label.val < 12+readSize+47+writerSize then
    BitOracleReturnLink.command writerLabel (some 3) (.compute (writerCode ⟨label.val-(12+readSize+47),by omega⟩))
  else if h : label.val < 12+readSize+47+writerSize+insertSize then
    BitOracleReturnLink.command insertLabel (some 9) (.compute (insertCode ⟨label.val-(12+readSize+47+writerSize),by omega⟩))
  else if h : label.val < 12+readSize+47+writerSize+insertSize+appendSize then
    BitOracleReturnLink.command appendLabel (some 10) (.compute (appendCode ⟨label.val-(12+readSize+47+writerSize+insertSize),by omega⟩))
  else
    let offset := label.val-(12+readSize+47+writerSize+insertSize+appendSize)
    have ho : offset < 6 := by have hl := label.isLt; unfold size at hl; omega
    let which : Fin 3 := ⟨offset/2,by omega⟩
    let phase : Fin 2 := ⟨offset%2,by omega⟩
    BitOracleReturnLink.command (copyLabel which) (some (![6,8,11] which))
      (.compute (copyCode which phase))

/-- Actual block inclusions discharge the return linker code premises. -/
theorem read_code (label : Fin readSize) : code (readLabel label) =
    BitOracleReturnLink.command readLabel (some 1) (.compute (readCode label)) := by
  have h0 : ¬ (readLabel label).val < 12 := by simp only [readLabel]; omega
  have ht : (readLabel label).val < 12+readSize := by simp only [readLabel]; omega
  rw [code,dif_neg h0,dif_pos ht]
  simp [readLabel]

theorem sample_code (label : Fin 47) : code (sampleLabel label) =
    BitOracleReturnLink.command sampleLabel (some 5) (CacheHashMachine.sampleCode label) := by
  have h0 : ¬ (sampleLabel label).val < 12 := by simp only [sampleLabel]; omega
  have h1 : ¬ (sampleLabel label).val < 12+readSize := by simp only [sampleLabel]; omega
  have ht : (sampleLabel label).val < 12+readSize+47 := by simp only [sampleLabel]; omega
  rw [code,dif_neg h0,dif_neg h1,dif_pos ht]
  simp [sampleLabel]

theorem writer_code (label : Fin writerSize) : code (writerLabel label) =
    BitOracleReturnLink.command writerLabel (some 3) (.compute (writerCode label)) := by
  have h0 : ¬ (writerLabel label).val < 12 := by simp only [writerLabel]; omega
  have h1 : ¬ (writerLabel label).val < 12+readSize := by simp only [writerLabel]; omega
  have h2 : ¬ (writerLabel label).val < 12+readSize+47 := by simp only [writerLabel]; omega
  have ht : (writerLabel label).val < 12+readSize+47+writerSize := by simp only [writerLabel]; omega
  rw [code,dif_neg h0,dif_neg h1,dif_neg h2,dif_pos ht]
  simp [writerLabel]

theorem insert_code (label : Fin insertSize) : code (insertLabel label) =
    BitOracleReturnLink.command insertLabel (some 9) (.compute (insertCode label)) := by
  have h0 : ¬ (insertLabel label).val < 12 := by simp only [insertLabel]; omega
  have h1 : ¬ (insertLabel label).val < 12+readSize := by simp only [insertLabel]; omega
  have h2 : ¬ (insertLabel label).val < 12+readSize+47 := by simp only [insertLabel]; omega
  have h3 : ¬ (insertLabel label).val < 12+readSize+47+writerSize := by simp only [insertLabel]; omega
  have ht : (insertLabel label).val < 12+readSize+47+writerSize+insertSize := by simp only [insertLabel]; omega
  rw [code,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos ht]
  simp [insertLabel]

theorem append_code (label : Fin appendSize) : code (appendLabel label) =
    BitOracleReturnLink.command appendLabel (some 10) (.compute (appendCode label)) := by
  have h0 : ¬ (appendLabel label).val < 12 := by simp only [appendLabel]; omega
  have h1 : ¬ (appendLabel label).val < 12+readSize := by simp only [appendLabel]; omega
  have h2 : ¬ (appendLabel label).val < 12+readSize+47 := by simp only [appendLabel]; omega
  have h3 : ¬ (appendLabel label).val < 12+readSize+47+writerSize := by simp only [appendLabel]; omega
  have h4 : ¬ (appendLabel label).val < 12+readSize+47+writerSize+insertSize := by simp only [appendLabel]; omega
  have ht : (appendLabel label).val < 12+readSize+47+writerSize+insertSize+appendSize := by simp only [appendLabel]; omega
  rw [code,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_pos ht]
  simp [appendLabel]

theorem copy_code (which : Fin 3) (label : Fin 2) : code (copyLabel which label) =
    BitOracleReturnLink.command (copyLabel which) (some (![6,8,11] which)) (.compute (copyCode which label)) := by
  have h0 : ¬ (copyLabel which label).val < 12 := by simp only [copyLabel]; omega
  have h1 : ¬ (copyLabel which label).val < 12+readSize := by simp only [copyLabel]; omega
  have h2 : ¬ (copyLabel which label).val < 12+readSize+47 := by simp only [copyLabel]; omega
  have h3 : ¬ (copyLabel which label).val < 12+readSize+47+writerSize := by simp only [copyLabel]; omega
  have h4 : ¬ (copyLabel which label).val < 12+readSize+47+writerSize+insertSize := by simp only [copyLabel]; omega
  have h5 : ¬ (copyLabel which label).val < 12+readSize+47+writerSize+insertSize+appendSize := by simp only [copyLabel]; omega
  rw [code,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5]
  fin_cases which <;> fin_cases label <;> rfl

open OracleComp in
/-- Clear one actual dispatcher work port, retaining every other word. The final
instruction executes its continuation statement and the exact charge is derived. -/
theorem clear_run (port : Fin 12) (again : Fin size)
    (next : Stmt (fun _ : Fin 12 => Bool) (Fin size) (Fin 3))
    (hcode : code again = .compute (clear port again next))
    (word : List Bool) (other : Fin 12 → List Bool) (memory : Fin 3) :
    run code (word.length+1) ⟨some again,memory,Function.update other port word⟩ =
      pure (stepAux next 0 (Function.update other port []),
        (word.length+1)*localCost (clear port again next)) := by
  induction word generalizing memory with
  | nil =>
    simp [run,BitOracleMachine.step,hcode,clear,stepAux,CoinWordLoader.encode]
  | cons bit word ih =>
    rw [List.length_cons,run]
    cases bit <;>
      simp [BitOracleMachine.step,hcode,clear,stepAux,CoinWordLoader.encode,ih,Nat.add_mul,Nat.add_comm]

/-- Original encoded key/cache/log and the local sampler record. The probe itself
moves the original cache from input work 0 to retained port 9. -/
def start (key cache log record : List Bool) : Config 12 size 3 :=
  ⟨some 0,0,![cache,[],[],[],[],[],[],[],key,[],log,record]⟩

def result (key cache log record value : List Bool) : Config 12 size 3 :=
  ⟨none,2,![[],[],[],[],[],[],[],value,key,cache,log,record]⟩

/-- An absent result is explicit, including exhausted fuel and rejected records. -/
def readout (cfg : Config 12 size 3) : Option (List Bool × List Bool × List Bool) :=
  if cfg.l = none ∧ cfg.var = 2 then some (cfg.stk 7,cfg.stk 9,cfg.stk 10) else none

end ExplainableCrypto.Helios.Computational.CacheHashDispatch
