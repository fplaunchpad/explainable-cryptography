import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
import ExplainableCrypto.Helios.Computational.PrimeProgrammedHistoryMachine

/-! Execute the first programmed cache transition and ordered history update
in the existing48 resident words. Later enclosing repacking remains separate. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgramMachine
open BitOracleMachine
abbrev prefixSize := PrimeProgrammedInsertMachine.size
abbrev size := prefixSize+PrimeProgrammedHistoryMachine.size

def prefixLabel (l : Fin prefixSize) : Fin size := ⟨l.val,by have := l.isLt; dsimp [size]; omega⟩
def tailLabel (l : Fin PrimeProgrammedHistoryMachine.size) : Fin size :=
  ⟨prefixSize+l.val,by have := l.isLt; dsimp [size]; omega⟩
def code (l : Fin size) : Command 48 size 3 :=
  if h : l.val < prefixSize then BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
    (PrimeProgrammedInsertMachine.code ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeProgrammedHistoryMachine.code ⟨l.val-prefixSize,by have := l.isLt; dsimp [size] at this; omega⟩)
abbrev Config := BitOracleMachine.Config 48 size 3
def start (old : Fin 48 → List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0)) (PrimeProgrammedInsertMachine.start old)
def clock (p q N : Nat) := PrimeProgrammedInsertMachine.clock p q N+PrimeProgrammedHistoryMachine.clock p N
def cost (p q N : Nat) := PrimeProgrammedInsertMachine.cost p q N+PrimeProgrammedHistoryMachine.cost p N

theorem prefix_code (l : Fin prefixSize) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (PrimeProgrammedInsertMachine.code l) := by
  have h : (prefixLabel l).val < prefixSize := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeProgrammedHistoryMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeProgrammedHistoryMachine.code l) := by
  have h : ¬ (tailLabel l).val < prefixSize := by dsimp [tailLabel]; omega
  simp only [code]
  rw [dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

theorem prefix_return (old : Fin 48 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (⟨none,2,old⟩ : PrimeProgrammedInsertMachine.Config) =
    BitOracleReturnLink.embed tailLabel none (PrimeProgrammedHistoryMachine.start old) := rfl

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
end ExplainableCrypto.Helios.Computational.PrimeProgramMachine
