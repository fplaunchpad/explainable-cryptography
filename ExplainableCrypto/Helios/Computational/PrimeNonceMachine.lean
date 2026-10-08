import ExplainableCrypto.Helios.Computational.SamplerOperands
import ExplainableCrypto.Helios.Computational.ScalarWriteCode

/-! Execute the nonzero-nonce successor using existing parsing, increment and
writing routines. Ports 5–7 are opaque saved words; port 4 retains the suffix.
Canonical input completeness is the interface, not malformed-input validation. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNonceMachine
open Turing.TM2
abbrev Config := BitOracleMachine.Config 8 26 3
abbrev Frame := Fin 3 → List Bool

def writerPorts : Fin 8 ≃ Fin 8 where
  toFun := ![1,5,2,3,0,4,6,7]
  invFun := ![4,0,2,3,5,1,6,7]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def writer := TM2FiniteCoordinates.program writerPorts (Equiv.refl _) (Equiv.refl _)
  ScalarWriteCode.program

def prepLabel (l : Fin 15) : Fin 26 := ⟨l.val+1,by omega⟩
def writeLabel (l : Fin 8) : Fin 26 := ⟨l.val+17,by omega⟩

def program (l : Fin 26) : Stmt (fun _ : Fin 8 => Bool) (Fin 26) (Fin 3) :=
  if l = 0 then .push 4 (fun _ => false) (.goto (fun _ => prepLabel 1))
  else if h : l.val < 16 then
    TM2ReturnLink.redirect prepLabel 16 (SamplerOperands.compiled ⟨l.val-1,by omega⟩)
  else if l = 16 then
    .pop 2 (fun _ b => CoinWordLoader.encode b)
      (.branch (fun v => v != 0) (.goto (fun _ => 16))
        (.load (fun _ => 0) (.goto (fun _ => writeLabel 5))))
  else if h : l.val < 25 then
    TM2ReturnLink.redirect writeLabel 25 (writer ⟨l.val-17,by omega⟩)
  else .halt

def start (word : List Bool) (frame : Frame) : Config :=
  ⟨some 0,0,![[],[],[],[],word,frame 0,frame 1,frame 2]⟩
def result (word : List Bool) (frame : Frame) : Config :=
  ⟨none,2,![[],[],[],[],word,frame 0,frame 1,frame 2]⟩
def clock (n : Nat) : Nat :=
  1+SamplerOperands.clock true 0 n+((n+1).size+1)+(3*(n+1).size+3)+1

end ExplainableCrypto.Helios.Computational.PrimeNonceMachine
