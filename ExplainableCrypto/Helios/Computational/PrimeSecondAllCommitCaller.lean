import ExplainableCrypto.Helios.Computational.PrimeSecondCommitTail
import ExplainableCrypto.Helios.Computational.PrimeSecondCommitCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondAllCommitCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 7557
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 65 ⊕ Fin 5 ≃ Fin 70 := finSumFinEquiv
def prefixCode : Code 70 PrimeSecondCommitCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSecondCommitCaller.code
def prefixLabel (l : Fin PrimeSecondCommitCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 5582 at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeSecondCommitTail.size) : Fin size :=
  ⟨5582+l.val,by have := l.isLt; change l.val < 1975 at this; unfold size; omega⟩
def code (l : Fin size) : Command 70 size 3 :=
  if h : l.val < 5582 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeSecondCommitTail.code ⟨l.val-5582,by have := l.isLt; unfold size at this; change l.val-5582 < 1975; omega⟩)
abbrev Config := BitOracleMachine.Config 70 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSecondCommitCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSecondCommitCaller.clock raw slack p q+PrimeSecondCommitTail.clock p q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSecondCommitCaller.cost raw slack p q+PrimeSecondCommitTail.cost p q

theorem prefix_code (l : Fin PrimeSecondCommitCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 5582 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeSecondCommitTail.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeSecondCommitTail.code l) := by
  have h : ¬ (tailLabel l).val < 5582 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds five blank outputs. The completed first p1 coordinate enters
the remaining commitment continuation with all previous 65 words retained. -/
theorem prefix_return (original : Fin 65 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSecondCommitCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSecondCommitTail.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeSecondCommitCaller.entry

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
  · have h := Finset.le_sup (f := fun k : Fin 70 =>
      ((BitOracleInitialInput.source (7 : Fin 70) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 70))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSecondAllCommitCaller
