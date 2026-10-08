import ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachine
import ExplainableCrypto.Helios.Computational.PrimeProgramCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 4327
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 48 ⊕ Fin 2 ≃ Fin 50 := finSumFinEquiv
def prefixCode : Code 50 PrimeProgramCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeProgramCaller.code
def prefixLabel (l : Fin PrimeProgramCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 4048 at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeProgramOutputMachine.size) : Fin size :=
  ⟨4048+l.val,by have := l.isLt; unfold PrimeProgramOutputMachine.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 50 size 3 :=
  if h : l.val < 4048 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel (PrimeProgramOutputMachine.natLabel 0 0)))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeProgramOutputMachine.code ⟨l.val-4048,by have := l.isLt; unfold size at this; change l.val-4048 < 279; omega⟩)
abbrev Config := BitOracleMachine.Config 50 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel (PrimeProgramOutputMachine.natLabel 0 0)))
    (BitOracleStackFrame.embed prefixLayout (PrimeProgramCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeProgramCaller.clock raw slack p q+PrimeProgramOutputMachine.clock p q raw.length
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeProgramCaller.cost raw slack p q+PrimeProgramOutputMachine.cost p q raw.length

theorem prefix_code (l : Fin PrimeProgramCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel (PrimeProgramOutputMachine.natLabel 0 0))) (prefixCode l) := by
  have h : (prefixLabel l).val < 4048 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeProgramOutputMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeProgramOutputMachine.code l) := by
  have h : ¬ (tailLabel l).val < 4048 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds only blank workspace. A completed prefix enters the actual
output encoder at its actual entry11 with all previous48 words and two blank outputs. -/
theorem prefix_return (original : Fin 48 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel (PrimeProgramOutputMachine.natLabel 0 0)))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeProgramCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeProgramOutputMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeProgramCaller.entry

/-- The only initialized word is the user's original encoded private input;
framing does not add prepared operands or a ready-state certificate. -/
theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7 (some entry) 0 raw := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length := by
  rw [start_source]
  unfold TM2TapeRuns.height
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : k = 7
    · subst k; simp [BitOracleInitialInput.source]
    · simp [BitOracleInitialInput.source,Function.update,h]
  · have h := Finset.le_sup (f := fun k : Fin 50 =>
      ((BitOracleInitialInput.source (7 : Fin 50) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 50))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputCaller
