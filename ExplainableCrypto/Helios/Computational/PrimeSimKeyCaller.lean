import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
import ExplainableCrypto.Helios.Computational.PrimeSimAllCommitCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 3653
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 43 ⊕ Fin 1 ≃ Fin 44 := finSumFinEquiv
def prefixCode : Code 44 PrimeSimAllCommitCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSimAllCommitCaller.code
def prefixLabel (l : Fin PrimeSimAllCommitCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeSimAllCommitCaller.size at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeSimKeyMachine.size) : Fin size :=
  ⟨3484+l.val,by have := l.isLt; unfold PrimeSimKeyMachine.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 44 size 3 :=
  if h : l.val < 3484 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeSimKeyMachine.code ⟨l.val-3484,by have := l.isLt; unfold size at this; omega⟩)
abbrev Config := BitOracleMachine.Config 44 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSimAllCommitCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSimAllCommitCaller.clock raw slack p q+PrimeSimKeyMachine.clock p
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSimAllCommitCaller.cost raw slack p q+PrimeSimKeyMachine.cost p

theorem prefix_code (l : Fin PrimeSimAllCommitCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 3484 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeSimKeyMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeSimKeyMachine.code l) := by
  have h : ¬ (tailLabel l).val < 3484 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds only blank workspace. A completed prefix enters the actual
key writer with exactly its previous 43 words and one empty output port. -/
theorem prefix_return (original : Fin 43 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSimAllCommitCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSimKeyMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeSimAllCommitCaller.entry

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
  · have h := Finset.le_sup (f := fun k : Fin 44 =>
      ((BitOracleInitialInput.source (7 : Fin 44) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 44))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSimKeyCaller
