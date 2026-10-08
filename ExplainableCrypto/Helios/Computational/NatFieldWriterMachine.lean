import ExplainableCrypto.Helios.Computational.CacheRoutineCode
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink

namespace ExplainableCrypto.Helios.Computational.NatFieldWriterMachine
open Turing.TM2 BitOracleMachine

def copyLabels : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun k := k == 1
  left_inv b := by cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl

def copyLayout : BitCopyMachine.Stack ⊕ Fin 4 ≃ Fin 7 where
  toFun | .inl .source => 0 | .inl .destination => 3 | .inl .scratch => 2
        | .inr k => ![1,4,5,6] k
  invFun := ![.inl .source,.inr 0,.inl .scratch,.inl .destination,.inr 1,.inr 2,.inr 3]
  left_inv k := by cases k with | inl k => cases k <;> rfl | inr k => fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def prefixLayout : FrameWriteMachine.Stack ⊕ Fin 2 ≃ Fin 7 where
  toFun | .inl (.inl .input) => 2 | .inl (.inl .count) => 6
        | .inl (.inl .scratch) => 5 | .inl (.inl .output) => 4
        | .inl (.inr _) => 3 | .inr k => ![0,1] k
  invFun := ![.inr 0,.inr 1,.inl (.inl .input),.inl (.inr ()),
    .inl (.inl .output),.inl (.inl .scratch),.inl (.inl .count)]
  left_inv k := by
    rcases k with ((k|u)|k)
    · cases k <;> rfl
    · cases u; rfl
    · fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def fieldLayout : FrameWriteMachine.Stack ⊕ Fin 2 ≃ Fin 7 :=
  prefixLayout.trans ((Equiv.swap 2 4).trans (Equiv.swap 2 1))

def copyProgram := TM2FiniteCoordinates.program (Equiv.refl (Fin 7)) copyLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate copyLayout (BitCopyMachine.program l))
def prefixProgram := TM2FiniteCoordinates.program (Equiv.refl (Fin 7)) CacheRoutineCode.writerLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate prefixLayout (FrameWriteMachine.program l))
def fieldProgram := TM2FiniteCoordinates.program (Equiv.refl (Fin 7)) CacheRoutineCode.writerLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate fieldLayout (FrameWriteMachine.program l))

def copyLabel (l : Fin 2) : Fin 21 := ⟨3+l.val,by omega⟩
def prefixLabel (l : Fin 8) : Fin 21 := ⟨5+l.val,by omega⟩
def fieldLabel (l : Fin 8) : Fin 21 := ⟨13+l.val,by omega⟩
private def enter (l : Fin 21) : Stmt (fun _ : Fin 7 => Bool) (Fin 21) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
private def guard (l : Fin 21) : Stmt (fun _ : Fin 7 => Bool) (Fin 21) (Fin 3) :=
  .branch (fun v => v == 2) (enter l) (.load (fun _ => 1) .halt)
def program (l : Fin 21) : Stmt (fun _ : Fin 7 => Bool) (Fin 21) (Fin 3) :=
  if l = 0 then guard (copyLabel 0)
  else if l = 1 then enter (prefixLabel 5)
  else if l = 2 then guard (fieldLabel 3)
  else if h : l.val < 5 then BitOracleReturnLink.stmt copyLabel (some 1) (copyProgram ⟨l.val-3,by omega⟩)
  else if h : l.val < 13 then BitOracleReturnLink.stmt prefixLabel (some 2) (prefixProgram (⟨l.val-5,by omega⟩ : Fin 8))
  else BitOracleReturnLink.stmt fieldLabel none (fieldProgram (⟨l.val-13,by omega⟩ : Fin 8))

def code : Code 7 21 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 7 21 3
def tick : Config → Config := TM2ReturnLink.tick program
def start (digits suffix : List Bool) : Config := ⟨some 0,2,![digits,suffix,[],[],[],[],[]]⟩
def encoded (n : Nat) (suffix : List Bool) :=
  uniformNatEncode (uniformNatEncode n).length ++ (uniformNatEncode n ++ suffix)
def result (digits word : List Bool) : Config := ⟨none,2,![digits,word,[],[],[],[],[]]⟩
def clock (n : Nat) := 5*n.size+8+FrameWriteMachine.cost (2*n.size+1)
def cost (n : Nat) := 32*clock n
end ExplainableCrypto.Helios.Computational.NatFieldWriterMachine
