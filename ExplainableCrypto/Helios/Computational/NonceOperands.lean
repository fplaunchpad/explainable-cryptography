import ExplainableCrypto.Helios.Computational.SamplerOperands
import ExplainableCrypto.Helios.Computational.BitCounterMachine

/-! Nonzero-nonce modulus preparation. Reuse the original slack/parser/width
instructions, executing predecessor before collecting the modulus width.
The public run contract covers canonical input with q ≥ 2. -/
namespace ExplainableCrypto.Helios.Computational.NonceOperands
open Turing.TM2
abbrev Label := SamplerOperands.Label
abbrev Frame := SamplerOperands.Frame
abbrev Config := SamplerOperands.Config
abbrev size : Nat := 15

def program : Label → Stmt (fun _ : Fin 8 => Bool) Label (Option Bool)
  | .parsed false => .branch (fun b => b == some true)
      (.goto (fun _ => .increment false)) (.load (fun _ => some false) .halt)
  | .increment b => TM2ReturnLink.redirect .increment .ready
      (TM2StackFrame.relocate SamplerOperands.layout (BitCounterMachine.program b))
  | l => SamplerOperands.program l

def tick (cfg : Config) : Config := TM2ReturnLink.tick program cfg
def compiled : Fin size → Stmt (fun _ : Fin 8 => Bool) (Fin size) (Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl _) SamplerOperands.labels BinaryModuloCode.memory program
def code : BitOracleMachine.Code 8 size 3 := fun l => .compute (compiled l)
def startWord (word : List Bool) : BitOracleMachine.Config 8 size 3 :=
  SamplerOperands.present (SamplerOperands.start false word (fun _ => []))
def result (slack q : Nat) (suffix : List Bool) (frame : Frame) : BitOracleMachine.Config 8 size 3 :=
  SamplerOperands.present (SamplerOperands.result slack (q-1) suffix frame)
def clock (slack q : Nat) : Nat := slack+5*q.size+2*(q-1).size+9
def cost (slack q : Nat) : Nat := 32*clock slack q

end ExplainableCrypto.Helios.Computational.NonceOperands
