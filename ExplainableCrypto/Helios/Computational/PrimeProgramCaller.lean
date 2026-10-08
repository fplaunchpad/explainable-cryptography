import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateCallerSource
import ExplainableCrypto.Helios.Computational.PrimeProgramMachine

/-! Original raw-input caller through the first executed programmed-state update. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgramCaller
open BitOracleMachine
set_option maxRecDepth 65536
abbrev prefixSize := PrimeProgrammedStateCaller.size
abbrev size := prefixSize+PrimeProgramMachine.size

def prefixLabel (l : Fin prefixSize) : Fin size := ⟨l.val,by have := l.isLt; dsimp [size]; omega⟩
def tailLabel (l : Fin PrimeProgramMachine.size) : Fin size :=
  ⟨prefixSize+l.val,by have := l.isLt; dsimp [size]; omega⟩
def code (l : Fin size) : Command 48 size 3 :=
  if h : l.val < prefixSize then BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
    (PrimeProgrammedStateCaller.code ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeProgramMachine.code ⟨l.val-prefixSize,by have := l.isLt; dsimp [size] at this; omega⟩)
abbrev Config := BitOracleMachine.Config 48 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0)) (PrimeProgrammedStateCaller.start raw)
def clock (raw : List Bool) (slack p q : Nat) := PrimeProgrammedStateCaller.clock raw slack p q+PrimeProgramMachine.clock p q raw.length
def cost (raw : List Bool) (slack p q : Nat) := PrimeProgrammedStateCaller.cost raw slack p q+PrimeProgramMachine.cost p q raw.length

theorem prefix_code (l : Fin prefixSize) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (PrimeProgrammedStateCaller.code l) := by
  have h : (prefixLabel l).val < prefixSize := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeProgramMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeProgramMachine.code l) := by
  have h : ¬ (tailLabel l).val < prefixSize := by dsimp [tailLabel]; omega
  simp only [code]
  rw [dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

theorem prefix_return (old : Fin 48 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (⟨none,2,old⟩ : PrimeProgrammedStateCaller.Config) =
    BitOracleReturnLink.embed tailLabel none (PrimeProgramMachine.start old) := rfl

def entry : Fin size := prefixLabel PrimeProgrammedStateCaller.entry
instance : NeZero size := ⟨by decide⟩

theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7 (some entry) 0 raw := by
  change BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (PrimeProgrammedStateCaller.start raw) = _
  rw [PrimeProgrammedStateCaller.start_source]
  rfl

theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length :=
  PrimeProgrammedStateCaller.start_height raw

#print axioms start_source
#print axioms start_height
#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
end ExplainableCrypto.Helios.Computational.PrimeProgramCaller
