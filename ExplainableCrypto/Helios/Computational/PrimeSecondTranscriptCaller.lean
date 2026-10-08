import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
import ExplainableCrypto.Helios.Computational.PrimeProgramOutputCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 5039
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 50 ⊕ Fin 9 ≃ Fin 59 := finSumFinEquiv
def prefixCode : Code 59 PrimeProgramOutputCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeProgramOutputCaller.code
def prefixLabel (l : Fin PrimeProgramOutputCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 4327 at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeSecondTranscriptMachine.size) : Fin size :=
  ⟨4327+l.val,by have := l.isLt; unfold PrimeSecondTranscriptMachine.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 59 size 3 :=
  if h : l.val < 4327 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeSecondTranscriptMachine.code ⟨l.val-4327,by have := l.isLt; unfold size at this; change l.val-4327 < 712; omega⟩)
abbrev Config := BitOracleMachine.Config 59 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeProgramOutputCaller.clock raw slack p q+PrimeSecondTranscriptMachine.clock slack p q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeProgramOutputCaller.cost raw slack p q+PrimeSecondTranscriptMachine.cost slack p q

theorem prefix_code (l : Fin PrimeProgramOutputCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 4327 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeSecondTranscriptMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeSecondTranscriptMachine.code l) := by
  have h : ¬ (tailLabel l).val < 4327 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing supplies the next transcript output words. A completed prefix enters the actual
second transcript controller at entry0 with all previous50 words and nine blank outputs. -/
theorem prefix_return (original : Fin 50 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeProgramOutputCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSecondTranscriptMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeProgramOutputCaller.entry

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
  · have h := Finset.le_sup (f := fun k : Fin 59 =>
      ((BitOracleInitialInput.source (7 : Fin 59) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 59))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptCaller
