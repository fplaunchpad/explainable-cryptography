import ExplainableCrypto.Helios.Computational.NatFieldWriterMachine

namespace ExplainableCrypto.Helios.Computational.BitPairWriterMachine
open Turing.TM2 BitOracleMachine
abbrev size := 23

def rightCopyLayout : BitCopyMachine.Stack ⊕ Fin 4 ≃ Fin 7 where
  toFun | .inl .source => 1 | .inl .destination => 3 | .inl .scratch => 4
        | .inr k => ![0,2,5,6] k
  invFun := ![.inr 0,.inl .source,.inr 1,.inl .destination,.inl .scratch,.inr 2,.inr 3]
  left_inv k := by cases k with | inl k => cases k <;> rfl | inr k => fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def copyLayout (phase : Fin 2) : BitCopyMachine.Stack ⊕ Fin 4 ≃ Fin 7 :=
  if phase=0 then rightCopyLayout else rightCopyLayout.trans (Equiv.swap 0 1)
def fieldLayout : FrameWriteMachine.Stack ⊕ Fin 2 ≃ Fin 7 where
  toFun | .inl (.inl .input) => 3 | .inl (.inl .count) => 4
        | .inl (.inl .scratch) => 5 | .inl (.inl .output) => 2
        | .inl (.inr _) => 6 | .inr k => ![0,1] k
  invFun := ![.inr 0,.inr 1,.inl (.inl .output),.inl (.inl .input),
    .inl (.inl .count),.inl (.inl .scratch),.inl (.inr ())]
  left_inv k := by
    rcases k with ((k|u)|k)
    · cases k <;> rfl
    · cases u; rfl
    · fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def copyProgram (phase : Fin 2) := TM2FiniteCoordinates.program (Equiv.refl (Fin 7))
  NatFieldWriterMachine.copyLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (copyLayout phase) (BitCopyMachine.program l))
def fieldProgram := TM2FiniteCoordinates.program (Equiv.refl (Fin 7))
  CacheRoutineCode.writerLabels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate fieldLayout (FrameWriteMachine.program l))
def copyLabel (phase : Fin 2) (l : Fin 2) : Fin size := ⟨3+2*phase.val+l.val,by dsimp [size]; omega⟩
def fieldLabel (phase : Fin 2) (l : Fin 8) : Fin size := ⟨7+8*phase.val+l.val,by dsimp [size]; omega⟩
def fieldReturn (phase : Fin 2) : Fin size := ⟨1+phase.val,by dsimp [size]; omega⟩
private def enter (l : Fin size) : Stmt (fun _ : Fin 7 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
private def fail : Stmt (fun _ : Fin 7 => Bool) (Fin size) (Fin 3) := .load (fun _ => 1) .halt
private def guard (next : Stmt (fun _ : Fin 7 => Bool) (Fin size) (Fin 3)) :=
  Stmt.branch (fun v => v == 2) next fail
private def finish : Stmt (fun _ : Fin 7 => Bool) (Fin size) (Fin 3) :=
  .push 2 (fun _ => true) (.push 2 (fun _ => false) (.push 2 (fun _ => false)
    (.push 2 (fun _ => true) (.push 2 (fun _ => true) (.load (fun _ => 2) .halt)))))
def program (l : Fin size) : Stmt (fun _ : Fin 7 => Bool) (Fin size) (Fin 3) :=
  if l=0 then guard (enter (copyLabel 0 0))
  else if l=1 then guard (enter (copyLabel 1 0))
  else if l=2 then guard finish
  else if h : l.val < 7 then
    let phase : Fin 2 := ⟨(l.val-3)/2,by omega⟩
    let k : Fin 2 := ⟨(l.val-3)%2,by omega⟩
    TM2ReturnLink.redirect (copyLabel phase) (fieldLabel phase 3) (copyProgram phase k)
  else
    let phase : Fin 2 := ⟨(l.val-7)/8,by dsimp [size] at *; omega⟩
    let k : Fin 8 := ⟨(l.val-7)%8,by omega⟩
    TM2ReturnLink.redirect (fieldLabel phase) (fieldReturn phase) (fieldProgram k)
def code : Code 7 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 7 size 3
def tick : Config → Config := TM2ReturnLink.tick program
def start (lhs rhs : List Bool) : Config := ⟨some 0,2,![lhs,rhs,[],[],[],[],[]]⟩
def result (lhs rhs : List Bool) : Config := ⟨none,2,![lhs,rhs,bitFieldsEncode [lhs,rhs],[],[],[],[]]⟩
def clock (L R : Nat) := 2*(L+R)+FrameWriteMachine.cost L+FrameWriteMachine.cost R+7
def cost (L R : Nat) := 32*clock L R
end ExplainableCrypto.Helios.Computational.BitPairWriterMachine
