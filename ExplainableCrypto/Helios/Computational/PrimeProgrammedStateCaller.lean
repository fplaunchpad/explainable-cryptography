import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
import ExplainableCrypto.Helios.Computational.PrimeSimKeyCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 3793
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 44 ⊕ Fin 4 ≃ Fin 48 := finSumFinEquiv
def prefixCode : Code 48 PrimeSimKeyCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSimKeyCaller.code
def prefixLabel (l : Fin PrimeSimKeyCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeSimKeyCaller.size at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeProgrammedStateInputMachine.size) : Fin size :=
  ⟨3653+l.val,by have := l.isLt; unfold PrimeProgrammedStateInputMachine.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 48 size 3 :=
  if h : l.val < 3653 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeProgrammedStateInputMachine.code ⟨l.val-3653,by have := l.isLt; unfold size at this; change l.val-3653 < 140; omega⟩)
abbrev Config := BitOracleMachine.Config 48 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSimKeyCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSimKeyCaller.clock raw slack p q+PrimeProgrammedStateInputMachine.clock raw.length
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSimKeyCaller.cost raw slack p q+PrimeProgrammedStateInputMachine.cost raw.length

theorem prefix_code (l : Fin PrimeSimKeyCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 3653 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeProgrammedStateInputMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeProgrammedStateInputMachine.code l) := by
  have h : ¬ (tailLabel l).val < 3653 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds only blank workspace. A completed prefix enters the actual
state extractor with exactly its previous 44 words and four empty output ports. -/
theorem prefix_return (original : Fin 44 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSimKeyCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeProgrammedStateInputMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeSimKeyCaller.entry

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
  · have h := Finset.le_sup (f := fun k : Fin 48 =>
      ((BitOracleInitialInput.source (7 : Fin 48) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 48))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateCaller
