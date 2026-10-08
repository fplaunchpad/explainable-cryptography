import ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 5582
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 59 ⊕ Fin 6 ≃ Fin 65 := finSumFinEquiv
def prefixCode : Code 65 PrimeSecondTranscriptCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSecondTranscriptCaller.code
def prefixLabel (l : Fin PrimeSecondTranscriptCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 5039 at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeSecondCommitMachine.size) : Fin size :=
  ⟨5039+l.val,by have := l.isLt; change l.val < 543 at this; unfold size; omega⟩
def code (l : Fin size) : Command 65 size 3 :=
  if h : l.val < 5039 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeSecondCommitMachine.code ⟨l.val-5039,by have := l.isLt; unfold size at this; change l.val-5039 < 543; omega⟩)
abbrev Config := BitOracleMachine.Config 65 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSecondTranscriptCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSecondTranscriptCaller.clock raw slack p q+PrimeSecondCommitMachine.clock p q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSecondTranscriptCaller.cost raw slack p q+PrimeSecondCommitMachine.cost p q

theorem prefix_code (l : Fin PrimeSecondTranscriptCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 5039 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeSecondCommitMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeSecondCommitMachine.code l) := by
  have h : ¬ (tailLabel l).val < 5039 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds six blank words. The completed second transcript enters the
actual commitment controller with all previous 59 words retained. -/
theorem prefix_return (original : Fin 59 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSecondTranscriptCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSecondCommitMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeSecondTranscriptCaller.entry

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
  · have h := Finset.le_sup (f := fun k : Fin 65 =>
      ((BitOracleInitialInput.source (7 : Fin 65) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 65))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitCaller
