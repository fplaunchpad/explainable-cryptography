import ExplainableCrypto.Helios.Computational.CacheHashDispatch

/-! Fixed four-field input routing for the proved cache request. This reuses the
original field parser and the existing twelve-port workspace. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestInput
open Turing.TM2 BitOracleMachine OracleComp

private def ports : NatPrefixMachine.Stack ≃ Fin 4 where
  toFun | .input => 0 | .count => 1 | .scratch => 2 | .output => 3
  invFun k := ![.input,.count,.scratch,.output] k
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def labels : FieldPrefixMachine.Label ≃ Fin 9 :=
  (List.Nodup.getEquivOfForallMemList CacheRoutineCode.fieldLabels
    (by decide +kernel) (by decide +kernel)).symm

def destination (phase : Fin 4) : Fin 12 := ![8,0,10,11] phase

/-- The unread input stays on 6; parser scratch is 1/2. Only the selected output
port is local; all other ports, including previously parsed fields, are framed. -/
def layout (phase : Fin 4) : NatPrefixMachine.Stack ⊕ Fin 8 ≃ Fin 12 :=
  ((Equiv.sumCongr ports (Equiv.refl _)).trans finSumFinEquiv).trans
    ((Equiv.swap 0 6).trans (Equiv.swap 3 (destination phase)))

def fieldCode (phase : Fin 4) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) labels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (layout phase) (FieldPrefixMachine.program l))

def fieldState (phase : Fin 4) (cfg : FieldPrefixMachine.Config) (frame : Fin 8 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl _) labels BinaryModuloCode.memory
    (TM2StackFrame.embed (layout phase) cfg frame)

private theorem field_cost : ∀ phase label, localCost (fieldCode phase label) ≤ 32 := by
  decide +kernel

/-- Place the existing field parser on its actual caller ports, preserving all
extra words and deriving the instruction charge. -/
theorem field_run (phase : Fin 4) (fuel : Nat) (cfg : FieldPrefixMachine.Config)
    (frame : Fin 8 → List Bool) :
    ∃ charge ≤ 32*fuel,
      run (fun l => .compute (fieldCode phase l)) fuel (fieldState phase cfg frame) =
      pure (fieldState phase (FieldPrefixMachine.tick^[fuel] cfg) frame,charge) := by
  obtain ⟨charge,hc,he⟩ := compute_run_cost (fieldCode phase) 32 (field_cost phase) fuel (fieldState phase cfg frame)
  refine ⟨charge,hc,?_⟩
  rw [he]
  congr 2
  rw [fieldState,fieldCode,TM2FiniteCoordinates.run,TM2StackFrame.run]
  rfl

def fieldLabel (phase : Fin 4) (label : Fin 9) : Fin 49 :=
  ⟨13+9*phase.val+label.val,by omega⟩

private def enter (next : Fin 49) : Stmt (fun _ : Fin 12 => Bool) (Fin 49) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
private def failure : Stmt (fun _ : Fin 12 => Bool) (Fin 49) (Fin 3) :=
  .load (fun _ => 0) .halt
private def success : Stmt (fun _ : Fin 12 => Bool) (Fin 49) (Fin 3) :=
  .load (fun _ => 2) .halt

/-- Literal original natural header for a four-field record. -/
def header (position : Fin 7) : Stmt (fun _ : Fin 12 => Bool) (Fin 49) (Fin 3) :=
  .pop 6 (fun _ b => CoinWordLoader.encode b)
    (.branch (fun v => v == (if (![true,true,true,false,false,false,true] position) then 2 else 1))
      (enter ⟨position.val+1,by omega⟩) failure)

def control (label : Fin 13) : Stmt (fun _ : Fin 12 => Bool) (Fin 49) (Fin 3) :=
  if h : label.val < 7 then header ⟨label.val,h⟩
  else if label.val == 7 then enter (fieldLabel 0 0)
  else if h : label.val < 11 then
    .branch (fun v => v == 2) (enter (fieldLabel ⟨label.val-7,by omega⟩ 0)) failure
  else if label.val == 11 then .branch (fun v => v == 2) (enter 12) failure
  else .peek 6 (fun _ b => CoinWordLoader.encode b) (.branch (fun v => v == 0) success failure)

/-- Successful parsing returns memory 2; rejected input returns memory 0. A
subsequent linker must check this flag before entering the cache dispatcher. -/
def code (label : Fin 49) : Command 12 49 3 :=
  if h : label.val < 13 then .compute (control ⟨label.val,h⟩)
  else
    let phase : Fin 4 := ⟨(label.val-13)/9,by omega⟩
    let localLabel : Fin 9 := ⟨(label.val-13)%9,by omega⟩
    BitOracleReturnLink.command (fieldLabel phase) (some ⟨8+phase.val,by omega⟩)
      (.compute (fieldCode phase localLabel))

def input (key cache log record : List Bool) : List Bool := bitFieldsEncode [key,cache,log,record]

def start (raw : List Bool) : Config 12 49 3 :=
  ⟨some 0,0,![[],[],[],[],[],[],raw,[],[],[],[],[]]⟩

def ready (key cache log record : List Bool) : Config 12 49 3 :=
  ⟨none,2,![cache,[],[],[],[],[],[],[],key,[],log,record]⟩

end ExplainableCrypto.Helios.Computational.CacheRequestInput
